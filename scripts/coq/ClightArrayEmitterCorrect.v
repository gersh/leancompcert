(* Generic semantic correctness of ClightArrayEmitterCompiler.

   A successful source denotation is replayed in CompCert's actual memory.
   The proof is symbolic in the loop count and uses flat_block_rel only as a
   simulation relation for one caller-supplied uint64_t array block. *)

From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightFragmentSem Direct.ClightDefinedOps.
Require Import Direct.ClightDSLCompiler Direct.ClightRolledCompiler.
Require Import Direct.ClightEmitterCompiler Direct.ClightEmitterCorrect.
Require Import Direct.ClightMemorySem Direct.ClightFlatSem.
Require Import Direct.ClightArrayEmitterCompiler.

Import ListNotations.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------- *)
(* Statement lists whose stores may change memory. *)

Inductive array_exec_stmt_list
    (fe: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
    (ge: genv) (en: env)
    : temp_env -> mem -> list statement -> temp_env -> mem -> outcome -> Prop :=
  | array_exec_stmt_list_nil: forall le m,
      array_exec_stmt_list fe ge en le m [] le m Out_normal
  | array_exec_stmt_list_cons_normal:
      forall le m s le1 m1 rest le2 m2 out,
      ClightBigstep.exec_stmt fe ge en le m s E0 le1 m1 Out_normal ->
      array_exec_stmt_list fe ge en le1 m1 rest le2 m2 out ->
      array_exec_stmt_list fe ge en le m (s :: rest) le2 m2 out
  | array_exec_stmt_list_cons_abrupt:
      forall le m s le1 m1 rest out,
      ClightBigstep.exec_stmt fe ge en le m s E0 le1 m1 out ->
      out <> Out_normal ->
      array_exec_stmt_list fe ge en le m (s :: rest) le1 m1 out.

Lemma array_exec_stmt_list_app_normal:
  forall fe ge en le m xs mid m1 ys le' m' out,
  array_exec_stmt_list fe ge en le m xs mid m1 Out_normal ->
  array_exec_stmt_list fe ge en mid m1 ys le' m' out ->
  array_exec_stmt_list fe ge en le m (xs ++ ys) le' m' out.
Proof.
  intros fe ge en le m xs mid m1 ys le' m' out X Y.
  remember Out_normal as normal eqn:EQ in X.
  induction X.
  - inversion EQ; subst. exact Y.
  - inversion EQ; subst. cbn. econstructor; eauto.
  - inversion EQ; subst. exfalso. apply H0. reflexivity.
Qed.

Lemma array_exec_stmt_list_sequence:
  forall fe ge en le m ss le' m' out,
  array_exec_stmt_list fe ge en le m ss le' m' out ->
  ClightBigstep.exec_stmt fe ge en le m (emitter_sequence ss)
    E0 le' m' out.
Proof.
  intros fe ge en le m ss le' m' out RUN.
  induction RUN.
  - apply exec_Sskip.
  - destruct rest as [|s' rest].
    + inversion RUN; subst. exact H.
    + cbn. change E0 with (E0 ** E0).
      eapply exec_Sseq_1; eauto.
  - destruct rest as [|s' rest].
    + exact H.
    + cbn. eapply exec_Sseq_2; eauto.
Qed.

Lemma scalar_exec_stmt_list_lift:
  forall fe ge en m le ss le' out,
  exec_stmt_list fe ge en m le ss le' out ->
  array_exec_stmt_list fe ge en le m ss le' m out.
Proof.
  intros fe ge en m le ss le' out RUN. induction RUN.
  - constructor.
  - econstructor; eauto.
  - eapply array_exec_stmt_list_cons_abrupt; eauto.
Qed.

(* -------------------------------------------------------------------- *)
(* State relation and pointer arithmetic. *)

Definition array_state_rel (l: array_emitter_layout) (n: nat)
    (b: block) (limit: Z) (source: adsl_state)
    (target: temp_env) (m: mem) : Prop :=
  emitter_regs_agree (ael_scalar l) n source.(ads_temps) target /\
  PTree.get (ael_base l) target = Some (Vptr b Ptrofs.zero) /\
  flat_block_rel source.(ads_cells) m b limit.

Lemma array_base_outside:
  forall l n,
  array_emitter_layout_wf l n ->
  forall r, (r < n)%nat -> ael_base l <> el_reg (ael_scalar l) r.
Proof.
  intros l n [LWF [BS [BC BR]]] r LT EQ.
  apply BR. rewrite EQ. now apply el_reg_in with (n := n).
Qed.

Lemma array_offset_exact:
  forall array_len index,
  0 <= array_len ->
  8 * array_len <= Ptrofs.modulus ->
  array_index_ok array_len index = true ->
  Ptrofs.unsigned
    (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 index)) =
  array_byte_offset index.
Proof.
  intros array_len index HLEN HFIT HINDEX.
  unfold array_index_ok in HINDEX. apply Z.ltb_lt in HINDEX.
  unfold array_byte_offset, Ptrofs.mul, Ptrofs.of_int64.
  assert (MOD64 : Ptrofs.modulus = Int64.modulus).
  { apply Ptrofs.modulus_eq64. reflexivity. }
  assert (UINDEX : Ptrofs.unsigned (Ptrofs.repr (Int64.unsigned index)) =
      Int64.unsigned index).
  { apply Ptrofs.unsigned_repr. split.
    - apply Int64.unsigned_range.
    - unfold Ptrofs.max_unsigned. rewrite MOD64.
      pose proof (Int64.unsigned_range index). lia. }
  assert (U8 : Ptrofs.unsigned (Ptrofs.repr 8) = 8).
  { apply Ptrofs.unsigned_repr. unfold Ptrofs.max_unsigned.
    rewrite MOD64. split; [lia|].
    change (8 <= 18446744073709551615). lia. }
  rewrite UINDEX, U8. apply Ptrofs.unsigned_repr.
  unfold Ptrofs.max_unsigned. split.
  - pose proof (Int64.unsigned_range index). nia.
  - assert (8 * Int64.unsigned index < Ptrofs.modulus) by nia.
    lia.
Qed.

Lemma array_offset_ok:
  forall array_len index,
  0 <= array_len ->
  array_index_ok array_len index = true ->
  flat_offset_ok (8 * array_len) (array_byte_offset index) = true.
Proof.
  intros array_len index HLEN HINDEX.
  unfold array_index_ok in HINDEX. apply Z.ltb_lt in HINDEX.
  unfold flat_offset_ok, array_byte_offset.
  repeat rewrite andb_true_iff. split; [split|].
  - apply Z.leb_le. pose proof (Int64.unsigned_range index). nia.
  - apply Z.leb_le. nia.
  - apply Z.eqb_eq. rewrite Z.mul_comm. apply Z.mod_mul. discriminate.
Qed.

Lemma eval_flat_array_address:
  forall ce b array_len cells target l n index_reg index,
  array_emitter_layout_wf l n ->
  (index_reg < n)%nat ->
  0 <= array_len ->
  8 * array_len <= Ptrofs.modulus ->
  array_index_ok array_len index = true ->
  PTree.get (ael_base l) target = Some (Vptr b Ptrofs.zero) ->
  PTree.get (el_reg (ael_scalar l) index_reg) target =
    Some (Vlong index) ->
  eval_flat ce b (8 * array_len) cells target
    (array_address l index_reg) =
    Some (Vptr b (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 index))).
Proof.
  intros ce b array_len cells target l n index_reg index LWF IR HLEN
    HFIT HINDEX HBASE HREG.
  unfold array_address. cbn [eval_flat]. rewrite HBASE, HREG.
  rewrite flat_checked_ptr_u64, flat_checked_long, sem_add_ptr_u64.
  apply flat_checked_ptr_u64.
Qed.

Lemma eval_flat_array_load:
  forall ce b array_len cells target l n dst index_reg index,
  array_emitter_layout_wf l n ->
  (dst < n)%nat -> (index_reg < n)%nat ->
  0 <= array_len ->
  8 * array_len <= Ptrofs.modulus ->
  array_index_ok array_len index = true ->
  PTree.get (ael_base l) target = Some (Vptr b Ptrofs.zero) ->
  PTree.get (el_reg (ael_scalar l) index_reg) target =
    Some (Vlong index) ->
  eval_flat ce b (8 * array_len) cells target
    (Ederef (array_address l index_reg) tulong) =
    Some (Vlong (flat_load cells (array_byte_offset index))).
Proof.
  intros ce b array_len cells target l n dst index_reg index LWF DST IR
    HLEN HFIT HINDEX HBASE HREG.
  cbn [eval_flat].
  rewrite (eval_flat_array_address ce b array_len cells target l n
    index_reg index LWF IR HLEN HFIT HINDEX HBASE HREG).
  rewrite same_block_refl.
  rewrite (array_offset_exact array_len index HLEN HFIT HINDEX).
  rewrite (array_offset_ok array_len index HLEN HINDEX).
  cbn. apply flat_checked_long.
Qed.

(* -------------------------------------------------------------------- *)
(* One source instruction and an instruction list. *)

Lemma exec_array_emitter_instr:
  forall fe ge en l n b array_len idx idx_expr i source target m source',
  array_emitter_layout_wf l n ->
  adinstr_wf n i ->
  typeof idx_expr = tulong ->
  emitter_index_expr (ael_scalar l) idx idx_expr ->
  array_state_rel l n b (8 * array_len) source target m ->
  eval_e (genv_cenv ge) m target idx_expr =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  0 <= array_len ->
  8 * array_len <= Ptrofs.modulus ->
  eval_adinstr array_len idx source i = Some source' ->
  exists target' m',
    array_exec_stmt_list fe ge en target m
      (array_emitter_instr l idx_expr i) target' m' Out_normal /\
    array_state_rel l n b (8 * array_len) source' target' m' /\
    PTree.get (el_counter (ael_scalar l)) target' =
      PTree.get (el_counter (ael_scalar l)) target.
Proof.
  intros fe ge en l n b array_len idx idx_expr i source target m source'
    LWF IWF IDXT IDXS REL IDX HLEN HFIT RUN.
  destruct REL as [AG [BASE MEM]].
  destruct source as [sourceTemps sourceCells].
  cbn [ads_temps ads_cells] in AG, MEM, RUN |- *.
  destruct i as [scalar|dst index_reg|index_reg source_reg].
  - cbn [eval_adinstr] in RUN.
    change (match eval_instr idx sourceTemps scalar with
      | Some temps => Some {| ads_temps := temps; ads_cells := sourceCells |}
      | None => None
      end = Some source') in RUN.
    destruct (eval_instr idx sourceTemps scalar) as [nextTemps|]
      eqn:STEP; try discriminate.
    inversion RUN; subst.
    destruct LWF as [SLWF [BS [BC BR]]].
    destruct (exec_emitter_instr fe ge en m (ael_scalar l) n idx idx_expr
      scalar sourceTemps target nextTemps SLWF IWF IDXT AG IDX STEP)
      as [target' [EXEC [AG' [COUNTER FRAME]]]].
    assert (BREG : forall r, (r < n)%nat ->
        ael_base l <> el_reg (ael_scalar l) r).
    { intros r LT EQ. apply BR. rewrite EQ.
      now apply el_reg_in with (n := n). }
    assert (BASE' : PTree.get (ael_base l) target' =
        Some (Vptr b Ptrofs.zero)).
    { rewrite (FRAME (ael_base l) BS BC BREG). exact BASE. }
    exists target', m. split.
    + apply scalar_exec_stmt_list_lift. exact EXEC.
    + split.
      * exact (conj AG' (conj BASE' MEM)).
      * exact COUNTER.
  - cbn [adinstr_wf eval_adinstr] in IWF, RUN.
    cbn [ads_temps ads_cells] in RUN.
    destruct IWF as [DST IR].
    destruct (PTree.get (reg_ident index_reg) sourceTemps)
      as [iv|] eqn:SINDEX; try discriminate.
    destruct iv; try discriminate.
    destruct (array_index_ok array_len i) eqn:SAFE; try discriminate.
    inversion RUN; subst.
    assert (TINDEX :
      PTree.get (el_reg (ael_scalar l) index_reg) target = Some (Vlong i)).
    { rewrite <- (AG index_reg IR). exact SINDEX. }
    set (loaded := flat_load sourceCells (array_byte_offset i)).
    set (target' := PTree.set (el_reg (ael_scalar l) dst)
      (Vlong loaded) target).
    set (flat0 := {| flat_temps := target; flat_array := sourceCells |}).
    set (flat' := {| flat_temps := target'; flat_array := sourceCells |}).
    assert (FLATRUN : run_flat_atom (genv_cenv ge) b (8 * array_len)
        (Sset (el_reg (ael_scalar l) dst)
          (Ederef (array_address l index_reg) tulong)) flat0 = Some flat').
    { cbv beta iota zeta delta
        [run_flat_atom run_flat_fuel flat0 flat_temps flat_array].
      rewrite (eval_flat_array_load (genv_cenv ge) b array_len sourceCells
        target l n dst index_reg i LWF DST IR HLEN HFIT SAFE BASE TINDEX).
      unfold flat', target', loaded. reflexivity. }
    assert (SUPPORTED : flat_stmt_supported
        (Sset (el_reg (ael_scalar l) dst)
          (Ederef (array_address l index_reg) tulong)) = true).
    { reflexivity. }
    destruct (run_flat_atom_sim fe ge en (genv_cenv ge) b
      (8 * array_len)
      (Sset (el_reg (ael_scalar l) dst)
        (Ederef (array_address l index_reg) tulong))
      flat0 m flat' eq_refl SUPPORTED MEM FLATRUN)
      as [m' [EXEC MEM']].
    assert (AG' : emitter_regs_agree (ael_scalar l) n
        (PTree.set (reg_ident dst) (Vlong loaded) sourceTemps) target').
    { unfold target', loaded. apply emitter_regs_agree_set; auto.
      exact (proj1 LWF). }
    assert (BASE' : PTree.get (ael_base l) target' =
        Some (Vptr b Ptrofs.zero)).
    { unfold target'. rewrite PTree.gso; auto.
      intro EQ. apply (array_base_outside l n LWF dst DST).
      exact EQ. }
    assert (COUNTER : PTree.get (el_counter (ael_scalar l)) target' =
        PTree.get (el_counter (ael_scalar l)) target).
    { unfold target'. exact
        (emitter_counter_preserved_set_reg (ael_scalar l) n target dst
          (Vlong loaded) (proj1 LWF) DST). }
    exists target', m'. split.
    + econstructor; [exact EXEC|constructor].
    + split.
      * exact (conj AG' (conj BASE' MEM')).
      * exact COUNTER.
  - cbn [adinstr_wf eval_adinstr] in IWF, RUN.
    cbn [ads_temps ads_cells] in RUN.
    destruct IWF as [IR SR].
    destruct (PTree.get (reg_ident index_reg) sourceTemps)
      as [iv|] eqn:SINDEX; try discriminate.
    destruct iv; try discriminate.
    destruct (PTree.get (reg_ident source_reg) sourceTemps)
      as [sv|] eqn:SVALUE; try discriminate.
    destruct sv; try discriminate.
    destruct (array_index_ok array_len i) eqn:SAFE; try discriminate.
    inversion RUN; subst.
    assert (TINDEX :
      PTree.get (el_reg (ael_scalar l) index_reg) target = Some (Vlong i)).
    { rewrite <- (AG index_reg IR). exact SINDEX. }
    assert (TVALUE :
      PTree.get (el_reg (ael_scalar l) source_reg) target = Some (Vlong i0)).
    { rewrite <- (AG source_reg SR). exact SVALUE. }
    set (cells' := flat_store sourceCells (array_byte_offset i) i0).
    set (flat0 := {| flat_temps := target; flat_array := sourceCells |}).
    set (flat' := {| flat_temps := target; flat_array := cells' |}).
    assert (FLATRUN : run_flat_atom (genv_cenv ge) b (8 * array_len)
        (Sassign (Ederef (array_address l index_reg) tulong)
          (Etempvar (el_reg (ael_scalar l) source_reg) tulong)) flat0 =
        Some flat').
    { cbv beta iota zeta delta
        [run_flat_atom run_flat_fuel flat0 flat_temps flat_array].
      rewrite (eval_flat_array_address (genv_cenv ge) b array_len
        sourceCells target l n index_reg i LWF IR HLEN HFIT SAFE BASE TINDEX).
      rewrite same_block_refl.
      rewrite (array_offset_exact array_len i HLEN HFIT SAFE).
      rewrite (array_offset_ok array_len i HLEN SAFE).
      cbn [eval_flat]. rewrite TVALUE, flat_checked_long, cast_u64_u64.
      unfold flat', cells'. reflexivity. }
    assert (SUPPORTED : flat_stmt_supported
        (Sassign (Ederef (array_address l index_reg) tulong)
          (Etempvar (el_reg (ael_scalar l) source_reg) tulong)) = true).
    { reflexivity. }
    destruct (run_flat_atom_sim fe ge en (genv_cenv ge) b
      (8 * array_len)
      (Sassign (Ederef (array_address l index_reg) tulong)
        (Etempvar (el_reg (ael_scalar l) source_reg) tulong))
      flat0 m flat' eq_refl SUPPORTED MEM FLATRUN)
      as [m' [EXEC MEM']].
    exists target, m'. split.
    + econstructor; [exact EXEC|constructor].
    + split.
      * exact (conj AG (conj BASE MEM')).
      * reflexivity.
Qed.

Lemma exec_array_emitter_instrs:
  forall fe ge en l n b array_len idx idx_expr is source target m source',
  array_emitter_layout_wf l n ->
  Forall (adinstr_wf n) is ->
  typeof idx_expr = tulong ->
  emitter_index_expr (ael_scalar l) idx idx_expr ->
  array_state_rel l n b (8 * array_len) source target m ->
  eval_e (genv_cenv ge) m target idx_expr =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  0 <= array_len ->
  8 * array_len <= Ptrofs.modulus ->
  eval_adinstrs array_len idx is source = Some source' ->
  exists target' m',
    array_exec_stmt_list fe ge en target m
      (array_emitter_instrs l idx_expr is) target' m' Out_normal /\
    array_state_rel l n b (8 * array_len) source' target' m' /\
    PTree.get (el_counter (ael_scalar l)) target' =
      PTree.get (el_counter (ael_scalar l)) target.
Proof.
  intros fe ge en l n b array_len idx idx_expr is.
  induction is as [|i rest IH];
    intros source target m source' LWF WF IDXT IDXS REL IDX HLEN HFIT RUN;
    cbn in RUN |- *.
  - inversion RUN; subst. exists target, m. split.
    + constructor.
    + split; [exact REL|reflexivity].
  - inversion WF as [|? ? IWF RESTWF]; subst.
    destruct (eval_adinstr array_len idx source i) as [source1|]
      eqn:STEP; try discriminate.
    destruct (exec_array_emitter_instr fe ge en l n b array_len idx
      idx_expr i source target m source1 LWF IWF IDXT IDXS REL IDX HLEN
      HFIT STEP) as [target1 [m1 [X1 [REL1 KEEP1]]]].
    assert (IDX1 : eval_e (genv_cenv ge) m1 target1 idx_expr =
        Some (Vlong (Int64.repr (Z.of_nat idx)))).
    { destruct IDXS as [STATIC|DYNAMIC].
      - subst idx_expr. reflexivity.
      - subst idx_expr. cbn [eval_e num_val] in IDX |- *.
        now rewrite KEEP1.
    }
    destruct (IH source1 target1 m1 source' LWF RESTWF IDXT IDXS REL1
      IDX1 HLEN HFIT RUN) as [target' [m' [XREST [REL' KEEP']]]].
    exists target', m'. split.
    + now apply array_exec_stmt_list_app_normal with (mid := target1)
        (m1 := m1).
    + split.
      * exact REL'.
      * now rewrite KEEP', KEEP1.
Qed.

(* -------------------------------------------------------------------- *)
(* The symbolic rolled loop, with memory threaded between iterations. *)

Lemma array_state_rel_set_counter:
  forall l n b limit source target m value,
  array_emitter_layout_wf l n ->
  array_state_rel l n b limit source target m ->
  array_state_rel l n b limit source
    (PTree.set (el_counter (ael_scalar l)) value target) m.
Proof.
  intros l n b limit source target m value LWF [AG [BASE MEM]].
  split.
  - apply emitter_regs_agree_set_counter; [exact (proj1 LWF)|exact AG].
  - split; [|exact MEM]. rewrite PTree.gso; auto.
    exact (proj1 (proj2 (proj2 LWF))).
Qed.

Theorem compile_array_emitter_loop_correct:
  forall fe ge en l n b array_len limit loop_limit body start count
      source target m source',
  array_emitter_layout_wf l n ->
  Forall (adinstr_wf n) body ->
  Z.of_nat limit < Int64.modulus ->
  loop_limit = Z.of_nat limit ->
  (start + count = limit)%nat ->
  0 <= array_len ->
  8 * array_len <= Ptrofs.modulus ->
  array_state_rel l n b (8 * array_len) source target m ->
  PTree.get (el_counter (ael_scalar l)) target =
    Some (Vlong (Int64.repr (Z.of_nat start))) ->
  eval_aloop array_len start count body source = Some source' ->
  exists target' m',
    ClightBigstep.exec_stmt fe ge en target m
      (array_emitter_loop l loop_limit body) E0 target' m' Out_normal /\
    array_state_rel l n b (8 * array_len) source' target' m' /\
    PTree.get (el_counter (ael_scalar l)) target' =
      Some (Vlong (Int64.repr (Z.of_nat limit))).
Proof.
  intros fe ge en l n b array_len limit loop_limit body start count.
  revert start.
  induction count as [|count IH];
    intros start source target m source' LWF WF FIT LIMIT SUM HLEN HFIT
      REL COUNTER LOOP.
  - cbn in LOOP. inversion LOOP; subst source'.
    assert (EQ : start = limit) by lia. subst start.
    destruct (emitter_test_false ge en m target (ael_scalar l)
      limit loop_limit COUNTER FIT LIMIT) as [TEST BOOL].
    exists target, m. split.
    + unfold array_emitter_loop, Swhile.
      eapply exec_Sloop_stop1.
      * eapply exec_Sseq_2.
        -- eapply exec_Sifthenelse with
             (v1 := Vint Int.zero) (b := false); eauto using exec_Sbreak.
        -- discriminate.
      * apply Out_break_or_return_B.
    + split; auto.
  - cbn in LOOP.
    destruct (eval_adinstrs array_len start body source)
      as [source1|] eqn:BODY; try discriminate.
    assert (IDXE : eval_e (genv_cenv ge) m target
        (Etempvar (el_counter (ael_scalar l)) tulong) =
        Some (Vlong (Int64.repr (Z.of_nat start)))).
    { now apply eval_e_emitter_counter. }
    destruct (exec_array_emitter_instrs fe ge en l n b array_len start
      (Etempvar (el_counter (ael_scalar l)) tulong) body source target m
      source1 LWF WF eq_refl (or_intror eq_refl) REL IDXE HLEN HFIT BODY)
      as [target1 [m1 [XBODY [REL1 KEEP]]]].
    assert (COUNTER1 : PTree.get (el_counter (ael_scalar l)) target1 =
        Some (Vlong (Int64.repr (Z.of_nat start)))).
    { now rewrite KEEP. }
    set (target2 := PTree.set (el_counter (ael_scalar l))
      (Vlong (Int64.repr (Z.of_nat (S start)))) target1).
    assert (XINC : ClightBigstep.exec_stmt fe ge en target1 m1
        (emitter_increment (ael_scalar l)) E0 target2 m1 Out_normal).
    { unfold target2. now apply emitter_increment_correct. }
    assert (XINCLIST : array_exec_stmt_list fe ge en target1 m1
        [emitter_increment (ael_scalar l)] target2 m1 Out_normal).
    { econstructor; [exact XINC|constructor]. }
    assert (XLOOPBODY : ClightBigstep.exec_stmt fe ge en target m
        (array_emitter_loop_body l body) E0 target2 m1 Out_normal).
    { unfold array_emitter_loop_body. apply array_exec_stmt_list_sequence.
      now apply array_exec_stmt_list_app_normal with (mid := target1)
        (m1 := m1). }
    assert (REL2 : array_state_rel l n b (8 * array_len)
        source1 target2 m1).
    { unfold target2. now apply array_state_rel_set_counter. }
    assert (COUNTER2 : PTree.get (el_counter (ael_scalar l)) target2 =
        Some (Vlong (Int64.repr (Z.of_nat (S start))))).
    { unfold target2. now rewrite PTree.gss. }
    assert (LT : (start < limit)%nat) by lia.
    destruct (emitter_test_true ge en m target (ael_scalar l) start limit
      loop_limit COUNTER LT FIT LIMIT) as [TEST BOOL].
    destruct (IH (S start) source1 target2 m1 source' LWF WF FIT LIMIT
      ltac:(lia) HLEN HFIT REL2 COUNTER2 LOOP)
      as [target' [m' [REST [REL' COUNTER']]]].
    exists target', m'. split.
    + unfold array_emitter_loop, Swhile in REST |- *.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop.
      * change E0 with (E0 ** E0).
        eapply exec_Sseq_1.
        -- eapply exec_Sifthenelse with
             (v1 := Vint Int.one) (b := true); eauto using exec_Sskip.
        -- exact XLOOPBODY.
      * apply Out_normal_or_continue_N.
      * apply exec_Sskip.
      * exact REST.
    + split; auto.
Qed.

(* -------------------------------------------------------------------- *)
(* Whole exact emitter body and function call. *)

Lemma eval_adinstrs_app:
  forall array_len idx xs ys st,
  eval_adinstrs array_len idx (xs ++ ys) st =
  match eval_adinstrs array_len idx xs st with
  | Some mid => eval_adinstrs array_len idx ys mid
  | None => None
  end.
Proof.
  intros array_len idx xs. induction xs as [|x rest IH];
    intros ys st; cbn; auto.
  destruct (eval_adinstr array_len idx st x); cbn; auto.
Qed.

Lemma array_emitter_instrs_app:
  forall l idx xs ys,
  array_emitter_instrs l idx (xs ++ ys) =
  array_emitter_instrs l idx xs ++ array_emitter_instrs l idx ys.
Proof.
  intros l idx xs. induction xs as [|x rest IH]; intros ys; cbn; auto.
  now rewrite IH, app_assoc.
Qed.

Lemma array_emitter_instrs_scalar:
  forall l idx xs,
  array_emitter_instrs l idx (map ADscalar xs) =
  emitter_instrs (ael_scalar l) idx xs.
Proof.
  intros l idx xs. induction xs as [|x rest IH]; cbn; auto.
  now rewrite IH.
Qed.

Lemma adsl_preamble_wf:
  forall n, Forall (adinstr_wf n) (adsl_preamble n).
Proof.
  intros n. unfold adsl_preamble.
  apply Forall_map. exact (preamble_wf n).
Qed.

Lemma initial_array_regs_agree:
  forall l n b,
  array_emitter_layout_wf l n ->
  emitter_regs_agree (ael_scalar l) n
    (create_undef_temps (temp_decls n))
    (PTree.set (ael_base l) (Vptr b Ptrofs.zero)
      (create_undef_temps (emitter_temp_decls (ael_scalar l)))).
Proof.
  intros l n b LWF r LT. rewrite PTree.gso.
  - exact (initial_emitter_regs_agree (ael_scalar l) n (proj1 LWF) r LT).
  - intro EQ. apply (array_base_outside l n LWF r LT). symmetry; exact EQ.
Qed.

Lemma array_params_temps_disjoint:
  forall l n,
  array_emitter_layout_wf l n ->
  list_disjoint [ael_base l]
    (var_names (emitter_temp_decls (ael_scalar l))).
Proof.
  intros l n [SLWF [BS [BC BR]]]. red.
  intros x y HX HY EQ. cbn in HX. destruct HX as [HX|HX]; [subst x|contradiction].
  subst y. unfold emitter_temp_decls, var_names in HY. cbn in HY.
  destruct HY as [SCRATCH|HY].
  - inversion SCRATCH. auto.
  - rewrite map_app in HY. cbn in HY.
    apply in_app_or in HY. destruct HY as [REGS|COUNTER].
    + rewrite map_map in REGS.
      rewrite map_id in REGS.
      exact (BR REGS).
    + cbn in COUNTER. destruct COUNTER as [COUNTER|CONTRA].
      * inversion COUNTER. auto.
      * contradiction.
Qed.

Lemma compile_array_emitted_rolled_body_correct:
  forall l loop_limit s p w fe ge en b m,
  array_emitter_source_matches s p ->
  array_emitter_layout_wf l (aes_reg_count s) ->
  adsl_wf p ->
  loop_limit = Z.of_nat (ap_loop_count p) ->
  adsl_denote p = Some w ->
  flat_block_rel (PTree.empty int64) m b (8 * ap_array_len p) ->
  exists le' m',
    ClightBigstep.exec_stmt fe ge en
      (PTree.set (ael_base l) (Vptr b Ptrofs.zero)
        (create_undef_temps
          (fn_temps (compile_array_emitted_rolled_program
            l loop_limit s))))
      m (fn_body (compile_array_emitted_rolled_program l loop_limit s))
      E0 le' m' (Out_return (Some (Vlong w, tulong))).
Proof.
  intros l loop_limit s p w fe ge en b m MATCH LAYOUT PWF LIMIT DEN MEM0.
  destruct MATCH as [MREG MINIT MBODY MEPI MOUT].
  assert (LWF : array_emitter_layout_wf l (ap_reg_count p)).
  { rewrite <- MREG. exact LAYOUT. }
  destruct PWF as [OUT INIT BODY EPI LOOPFIT ALEN AFIT].
  unfold adsl_denote in DEN.
  destruct (eval_adinstrs (ap_array_len p) 0
      (adsl_preamble (ap_reg_count p) ++ ap_init p)
      (adsl_initial_state p)) as [source1|] eqn:PREFIX; try discriminate.
  destruct (eval_aloop (ap_array_len p) 0 (ap_loop_count p)
      (ap_body p) source1) as [source2|] eqn:LOOP; try discriminate.
  destruct (eval_adinstrs (ap_array_len p) 0 (ap_epilogue p) source2)
      as [source3|] eqn:EPILOGUE; try discriminate.
  destruct (PTree.get (reg_ident (ap_output p)) source3.(ads_temps))
      as [v|] eqn:OUTPUT; try discriminate.
  destruct v; try discriminate. inversion DEN; subst i.

  rewrite eval_adinstrs_app in PREFIX.
  destruct (eval_adinstrs (ap_array_len p) 0
      (adsl_preamble (ap_reg_count p)) (adsl_initial_state p))
      as [sourcep|] eqn:PREAMBLE; try discriminate.

  set (target0 := PTree.set (ael_base l) (Vptr b Ptrofs.zero)
    (create_undef_temps (emitter_temp_decls (ael_scalar l)))).
  assert (AG0 : emitter_regs_agree (ael_scalar l) (ap_reg_count p)
      (adsl_initial_state p).(ads_temps) target0).
  { unfold target0, adsl_initial_state. cbn [ads_temps].
    now apply initial_array_regs_agree. }
  assert (BASE0 : PTree.get (ael_base l) target0 =
      Some (Vptr b Ptrofs.zero)).
  { unfold target0. now rewrite PTree.gss. }
  assert (REL0 : array_state_rel l (ap_reg_count p) b
      (8 * ap_array_len p) (adsl_initial_state p) target0 m).
  { exact (conj AG0 (conj BASE0 MEM0)). }

  set (targets := PTree.set (el_scratch (ael_scalar l))
    (Vint Int.zero) target0).
  assert (XSCRATCH : ClightBigstep.exec_stmt fe ge en target0 m
      (emitter_scratch_zero (ael_scalar l)) E0 targets m Out_normal).
  { unfold emitter_scratch_zero, targets. apply exec_Sset.
    apply eval_e_sound. reflexivity. }
  assert (RELS : array_state_rel l (ap_reg_count p) b
      (8 * ap_array_len p) (adsl_initial_state p) targets m).
  { destruct REL0 as [AG [BASE MEM]]. split.
    - unfold targets. apply emitter_regs_agree_set_scratch;
        auto using (proj1 LWF).
    - split; [|exact MEM]. unfold targets. rewrite PTree.gso; auto.
      exact (proj1 (proj2 LWF)). }
  assert (STATIC0 : eval_e (genv_cenv ge) m targets
      (Econst_long Int64.zero tulong) =
      Some (Vlong (Int64.repr (Z.of_nat 0)))) by reflexivity.
  destruct (exec_array_emitter_instrs fe ge en l (ap_reg_count p) b
      (ap_array_len p) 0 (Econst_long Int64.zero tulong)
      (adsl_preamble (ap_reg_count p)) (adsl_initial_state p) targets m
      sourcep LWF (adsl_preamble_wf _) eq_refl (or_introl eq_refl) RELS
      STATIC0 ALEN AFIT PREAMBLE)
    as [targetp [mp [XPRE [RELP KEEPP]]]].

  set (targetc1 := PTree.set (el_counter (ael_scalar l))
    (Vlong Int64.zero) targetp).
  assert (XCOUNTER1 : ClightBigstep.exec_stmt fe ge en targetp mp
      (emitter_counter_zero (ael_scalar l)) E0 targetc1 mp Out_normal).
  { unfold emitter_counter_zero, targetc1. apply exec_Sset.
    apply eval_Econst_long. }
  assert (RELC1 : array_state_rel l (ap_reg_count p) b
      (8 * ap_array_len p) sourcep targetc1 mp).
  { unfold targetc1. now apply array_state_rel_set_counter. }
  assert (STATIC1 : eval_e (genv_cenv ge) mp targetc1
      (Econst_long Int64.zero tulong) =
      Some (Vlong (Int64.repr (Z.of_nat 0)))) by reflexivity.
  destruct (exec_array_emitter_instrs fe ge en l (ap_reg_count p) b
      (ap_array_len p) 0 (Econst_long Int64.zero tulong) (ap_init p)
      sourcep targetc1 mp source1 LWF INIT eq_refl (or_introl eq_refl)
      RELC1 STATIC1 ALEN AFIT PREFIX)
    as [target1a [m1 [XINIT [REL1a KEEPINIT]]]].

  set (target1 := PTree.set (el_counter (ael_scalar l))
    (Vlong Int64.zero) target1a).
  assert (XCOUNTER2 : ClightBigstep.exec_stmt fe ge en target1a m1
      (emitter_counter_zero (ael_scalar l)) E0 target1 m1 Out_normal).
  { unfold emitter_counter_zero, target1. apply exec_Sset.
    apply eval_Econst_long. }
  assert (REL1 : array_state_rel l (ap_reg_count p) b
      (8 * ap_array_len p) source1 target1 m1).
  { unfold target1. now apply array_state_rel_set_counter. }
  assert (COUNTER1 : PTree.get (el_counter (ael_scalar l)) target1 =
      Some (Vlong (Int64.repr (Z.of_nat 0)))).
  { unfold target1. now rewrite PTree.gss. }

  destruct (compile_array_emitter_loop_correct fe ge en l
      (ap_reg_count p) b (ap_array_len p) (ap_loop_count p) loop_limit
      (ap_body p) 0 (ap_loop_count p) source1 target1 m1 source2
      LWF BODY LOOPFIT LIMIT ltac:(lia) ALEN AFIT REL1 COUNTER1 LOOP)
    as [target2 [m2 [XLOOP [REL2 COUNTER2]]]].

  assert (STATIC_EPI : eval_e (genv_cenv ge) m2 target2
      (Econst_long Int64.zero tulong) =
      Some (Vlong (Int64.repr (Z.of_nat 0)))) by reflexivity.
  destruct (exec_array_emitter_instrs fe ge en l (ap_reg_count p) b
      (ap_array_len p) 0 (Econst_long Int64.zero tulong) (ap_epilogue p)
      source2 target2 m2 source3 LWF EPI eq_refl (or_introl eq_refl)
      REL2 STATIC_EPI ALEN AFIT EPILOGUE)
    as [target3 [m3 [XEPI [REL3 KEEPEPI]]]].
  destruct REL3 as [AG3 [BASE3 MEM3]].
  assert (TOUTPUT : PTree.get (el_reg (ael_scalar l) (ap_output p))
      target3 = Some (Vlong w)).
  { rewrite <- (AG3 (ap_output p) OUT). exact OUTPUT. }
  assert (XRETURN : ClightBigstep.exec_stmt fe ge en target3 m3
      (Sreturn (Some
        (Etempvar (el_reg (ael_scalar l) (ap_output p)) tulong)))
      E0 target3 m3 (Out_return (Some (Vlong w, tulong)))).
  { apply exec_Sreturn_some. now apply eval_Etempvar. }

  assert (XSCRATCHS : array_exec_stmt_list fe ge en target0 m
      [emitter_scratch_zero (ael_scalar l)] targets m Out_normal).
  { econstructor; [exact XSCRATCH|constructor]. }
  assert (XCOUNTER1S : array_exec_stmt_list fe ge en targetp mp
      [emitter_counter_zero (ael_scalar l)] targetc1 mp Out_normal).
  { econstructor; [exact XCOUNTER1|constructor]. }
  assert (XCOUNTER2S : array_exec_stmt_list fe ge en target1a m1
      [emitter_counter_zero (ael_scalar l)] target1 m1 Out_normal).
  { econstructor; [exact XCOUNTER2|constructor]. }
  assert (XLOOPS : array_exec_stmt_list fe ge en target1 m1
      [array_emitter_loop l loop_limit (ap_body p)] target2 m2 Out_normal).
  { econstructor; [exact XLOOP|constructor]. }
  assert (XRETURNS : array_exec_stmt_list fe ge en target3 m3
      [Sreturn (Some
        (Etempvar (el_reg (ael_scalar l) (ap_output p)) tulong))]
      target3 m3 (Out_return (Some (Vlong w, tulong)))).
  { eapply array_exec_stmt_list_cons_abrupt;
      [exact XRETURN|discriminate]. }

  assert (XALL : array_exec_stmt_list fe ge en target0 m
      (array_emitter_body_statements l loop_limit s) target3 m3
      (Out_return (Some (Vlong w, tulong)))).
  { unfold array_emitter_body_statements, array_emitter_preamble.
    rewrite MREG, MINIT, MBODY, MEPI, MOUT.
    unfold adsl_preamble in XPRE.
    rewrite (array_emitter_instrs_scalar l
      (Econst_long Int64.zero tulong) (preamble (ap_reg_count p))) in XPRE.
    repeat rewrite <- app_assoc.
    apply array_exec_stmt_list_app_normal with (mid := targets) (m1 := m).
    - exact XSCRATCHS.
    - apply array_exec_stmt_list_app_normal with (mid := targetp) (m1 := mp).
      + exact XPRE.
      + apply array_exec_stmt_list_app_normal with
          (mid := targetc1) (m1 := mp).
        * exact XCOUNTER1S.
        * apply array_exec_stmt_list_app_normal with
            (mid := target1a) (m1 := m1).
          -- exact XINIT.
          -- apply array_exec_stmt_list_app_normal with
               (mid := target1) (m1 := m1).
             ++ exact XCOUNTER2S.
             ++ apply array_exec_stmt_list_app_normal with
                  (mid := target2) (m1 := m2).
                ** exact XLOOPS.
                ** apply array_exec_stmt_list_app_normal with
                     (mid := target3) (m1 := m3); auto. }

  exists target3, m3.
  change (ClightBigstep.exec_stmt fe ge en target0 m
    (compile_array_emitted_rolled_body l loop_limit s) E0 target3 m3
    (Out_return (Some (Vlong w, tulong)))).
  unfold compile_array_emitted_rolled_body.
  now apply array_exec_stmt_list_sequence.
Qed.

Theorem compile_array_emitted_rolled_program_correct:
  forall l loop_limit s p w ge b m,
  array_emitter_source_matches s p ->
  array_emitter_layout_wf l (aes_reg_count s) ->
  adsl_wf p ->
  loop_limit = Z.of_nat (ap_loop_count p) ->
  adsl_denote p = Some w ->
  flat_block_rel (PTree.empty int64) m b (8 * ap_array_len p) ->
  exists m',
    ClightBigstep.eval_funcall function_entry2 ge m
      (Internal (compile_array_emitted_rolled_program l loop_limit s))
      [Vptr b Ptrofs.zero] E0 m' (Vlong w).
Proof.
  intros l loop_limit s p w ge b m MATCH LWF PWF LIMIT DEN MEM.
  destruct (compile_array_emitted_rolled_body_correct l loop_limit s p w
    function_entry2 ge empty_env b m MATCH LWF PWF LIMIT DEN MEM)
    as [le' [m' BODY]].
  exists m'. eapply eval_funcall_internal with
    (e := empty_env)
    (le1 := PTree.set (ael_base l) (Vptr b Ptrofs.zero)
      (create_undef_temps
        (fn_temps (compile_array_emitted_rolled_program l loop_limit s))))
    (le2 := le') (m1 := m) (m2 := m')
    (out := Out_return (Some (Vlong w, tulong))).
  - constructor.
    + constructor.
    + constructor; [intro CONTRA; inversion CONTRA|constructor].
    + apply array_params_temps_disjoint with (n := aes_reg_count s).
      exact LWF.
    + constructor.
    + reflexivity.
  - exact BODY.
  - simpl. split; [discriminate|reflexivity].
  - reflexivity.
Qed.

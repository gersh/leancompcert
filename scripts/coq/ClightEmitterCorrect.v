(* Semantic correctness of the exact emitter-shaped rolled Clight compiler.

   The compiler itself lives in [ClightEmitterCompiler].  This file proves,
   once and for all and without reducing a concrete loop bound, that its
   compact [Swhile] program implements [dsl_denote]. *)

From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightFragmentSem Direct.ClightDefinedOps.
Require Import Direct.ClightDSLCompiler Direct.ClightRolledCompiler.
Require Import Direct.ClightEmitterCompiler.

Import ListNotations.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------- *)
(* Executing the exact right-associated statement list emitted by clightgen. *)

Inductive exec_stmt_list
    (fe: genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
    (ge: genv) (en: env) (m: mem)
    : temp_env -> list statement -> temp_env -> outcome -> Prop :=
  | exec_stmt_list_nil: forall le,
      exec_stmt_list fe ge en m le [] le Out_normal
  | exec_stmt_list_cons_normal: forall le s le1 rest le2 out,
      ClightBigstep.exec_stmt fe ge en le m s E0 le1 m Out_normal ->
      exec_stmt_list fe ge en m le1 rest le2 out ->
      exec_stmt_list fe ge en m le (s :: rest) le2 out
  | exec_stmt_list_cons_abrupt: forall le s le1 rest out,
      ClightBigstep.exec_stmt fe ge en le m s E0 le1 m out ->
      out <> Out_normal ->
      exec_stmt_list fe ge en m le (s :: rest) le1 out.

Lemma exec_stmt_list_app_normal:
  forall fe ge en m le xs mid ys le' out,
  exec_stmt_list fe ge en m le xs mid Out_normal ->
  exec_stmt_list fe ge en m mid ys le' out ->
  exec_stmt_list fe ge en m le (xs ++ ys) le' out.
Proof.
  intros fe ge en m le xs mid ys le' out X Y.
  remember Out_normal as normal eqn:EQ in X.
  induction X.
  - inversion EQ; subst. exact Y.
  - inversion EQ; subst. cbn. econstructor; eauto.
  - inversion EQ; subst. exfalso. apply H0. reflexivity.
Qed.

Lemma exec_stmt_list_sequence:
  forall fe ge en m le ss le' out,
  exec_stmt_list fe ge en m le ss le' out ->
  ClightBigstep.exec_stmt fe ge en le m (emitter_sequence ss)
    E0 le' m out.
Proof.
  intros fe ge en m le ss le' out RUN.
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

(* -------------------------------------------------------------------- *)
(* Operand and expression correspondence under the layout renaming. *)

Lemma typeof_emitter_operand:
  forall l idx o,
  typeof idx = tulong -> typeof (emitter_operand l idx o) = tulong.
Proof. intros l idx o TY; destruct o; cbn; auto. Qed.

Lemma eval_e_emitter_operand:
  forall ce m l n idx idx_expr source target o w,
  doperand_wf n o ->
  emitter_regs_agree l n source target ->
  eval_e ce m target idx_expr =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_operand idx source o = Some w ->
  eval_e ce m target (emitter_operand l idx_expr o) = Some (Vlong w).
Proof.
  intros ce m l n idx idx_expr source target o w WF AG IDX EVAL.
  destruct o; cbn in WF, EVAL |- *.
  - destruct (PTree.get (reg_ident r) source) as [v|] eqn:G;
      try discriminate.
    destruct v; try discriminate. inversion EVAL; subst.
    rewrite <- (AG r WF), G. reflexivity.
  - inversion EVAL; reflexivity.
  - inversion EVAL; subst. exact IDX.
Qed.

Definition emitter_binop_expr (l: emitter_layout) (idx_expr: expr)
    (op: dop) (lhs rhs: doperand) : expr :=
  Ebinop (cop_of_dop op)
    (emitter_operand l idx_expr lhs) (emitter_operand l idx_expr rhs)
    (dop_result_type op).

Lemma eval_e_emitter_binop:
  forall ce m l n idx idx_expr source target op lhs rhs a b,
  doperand_wf n lhs -> doperand_wf n rhs ->
  typeof idx_expr = tulong ->
  emitter_regs_agree l n source target ->
  eval_e ce m target idx_expr =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_operand idx source lhs = Some a ->
  eval_operand idx source rhs = Some b ->
  eval_e ce m target (emitter_binop_expr l idx_expr op lhs rhs) =
    eval_u64_binop (cop_of_dop op) a b.
Proof.
  intros ce m l n idx idx_expr source target op lhs rhs a b
    LWF RWF IDXT AG IDX HL HR.
  unfold emitter_binop_expr; cbn [eval_e].
  rewrite (eval_e_emitter_operand ce m l n idx idx_expr source target
    lhs a LWF AG IDX HL).
  rewrite (eval_e_emitter_operand ce m l n idx idx_expr source target
    rhs b RWF AG IDX HR).
  rewrite !typeof_emitter_operand by exact IDXT.
  assert (BOK : binop_ok (cop_of_dop op) tulong tulong = true)
    by (destruct op; reflexivity).
  rewrite BOK, sem_binary_operation_u64_exact.
  destruct op;
    cbn [cop_of_dop eval_u64_binop num_val Vtrue Vfalse];
    repeat match goal with
    | |- context [if ?c then _ else _] => destruct c
    end;
    try reflexivity.
  all: unfold Val.of_bool; destruct (Int64.cmpu _ a b); reflexivity.
Qed.

Lemma eval_e_emitter_arithmetic:
  forall ce m l n idx idx_expr source target op lhs rhs a b w,
  dop_is_comparison op = false ->
  doperand_wf n lhs -> doperand_wf n rhs ->
  typeof idx_expr = tulong ->
  emitter_regs_agree l n source target ->
  eval_e ce m target idx_expr =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_operand idx source lhs = Some a ->
  eval_operand idx source rhs = Some b ->
  eval_dop op a b = Some w ->
  eval_e ce m target (emitter_binop_expr l idx_expr op lhs rhs) =
    Some (Vlong w).
Proof.
  intros ce m l n idx idx_expr source target op lhs rhs a b w CMP
    LWF RWF IDXT AG IDX HL HR OP.
  rewrite (eval_e_emitter_binop ce m l n idx idx_expr source target
    op lhs rhs a b LWF RWF IDXT AG IDX HL HR).
  unfold eval_dop in OP.
  destruct op; cbn in CMP, OP |- *; try discriminate;
    repeat match goal with
    | H : context [if ?c then _ else _] |- _ => destruct c eqn:?
    end;
    try discriminate;
    inversion OP; reflexivity.
Qed.

Definition int_of_bool (q: bool) : int := if q then Int.one else Int.zero.

Lemma eval_u64_comparison_shape:
  forall op a b,
  dop_is_comparison op = true ->
  exists q,
    eval_u64_binop (cop_of_dop op) a b = Some (Val.of_bool q).
Proof.
  intros op a b CMP. destruct op; cbn in CMP; try discriminate;
    eexists; reflexivity.
Qed.

Lemma val_u64_of_bool:
  forall q,
  val_u64 (Val.of_bool q) =
    Some (Int64.repr (Int.unsigned (int_of_bool q))).
Proof. intros []; reflexivity. Qed.

Lemma typeof_emitter_comparison:
  forall l idx_expr op lhs rhs,
  dop_is_comparison op = true ->
  typeof (emitter_binop_expr l idx_expr op lhs rhs) = tint.
Proof. intros l idx_expr op lhs rhs CMP; destruct op; discriminate || reflexivity. Qed.

Lemma eval_e_narrow_bool:
  forall ce m target e q,
  typeof e = tint ->
  eval_e ce m target e = Some (Val.of_bool q) ->
  eval_e ce m target (Ecast e tuchar) = Some (Vint (int_of_bool q)).
Proof.
  intros ce m target e [] TY RUN;
    cbn [eval_e int_of_bool Val.of_bool Vtrue Vfalse];
    rewrite RUN, TY; reflexivity.
Qed.

Lemma eval_e_emitter_comparison_narrow:
  forall ce m l n idx idx_expr source target op lhs rhs a b w,
  dop_is_comparison op = true ->
  doperand_wf n lhs -> doperand_wf n rhs ->
  typeof idx_expr = tulong ->
  emitter_regs_agree l n source target ->
  eval_e ce m target idx_expr =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_operand idx source lhs = Some a ->
  eval_operand idx source rhs = Some b ->
  eval_dop op a b = Some w ->
  exists i,
    eval_e ce m target
      (Ecast (emitter_binop_expr l idx_expr op lhs rhs) tuchar) =
      Some (Vint i) /\
    Int64.repr (Int.unsigned i) = w.
Proof.
  intros ce m l n idx idx_expr source target op lhs rhs a b w CMP
    LWF RWF IDXT AG IDX HL HR OP.
  pose proof (eval_e_emitter_binop ce m l n idx idx_expr source target
    op lhs rhs a b LWF RWF IDXT AG IDX HL HR) as RAW.
  destruct (eval_u64_comparison_shape op a b CMP) as [q SHAPE].
  assert (RAWQ : eval_e ce m target
      (emitter_binop_expr l idx_expr op lhs rhs) = Some (Val.of_bool q)).
  { rewrite RAW. exact SHAPE. }
  unfold eval_dop in OP.
  rewrite SHAPE, val_u64_of_bool in OP. inversion OP; subst w.
  exists (int_of_bool q). split.
  - apply eval_e_narrow_bool.
    + now apply typeof_emitter_comparison.
    + exact RAWQ.
  - reflexivity.
Qed.

Lemma eval_e_emitter_scratch_widen:
  forall ce m l target i,
  PTree.get (el_scratch l) target = Some (Vint i) ->
  eval_e ce m target
    (Ecast (Etempvar (el_scratch l) tuchar) tulong) =
    Some (Vlong (Int64.repr (Int.unsigned i))).
Proof.
  intros ce m l target i GET.
  cbn [eval_e num_val]. rewrite GET.
  reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* Exact one-instruction and instruction-list simulation. *)

Lemma emitter_counter_preserved_set_reg:
  forall l n (target: temp_env) dst (v: val),
  emitter_layout_wf l n -> (dst < n)%nat ->
  PTree.get (el_counter l) (PTree.set (el_reg l dst) v target) =
    PTree.get (el_counter l) target.
Proof.
  intros l n target dst v WF DST. rewrite PTree.gso; auto.
  intro E. apply (el_reg_ne_counter l n dst WF DST). symmetry; exact E.
Qed.

Lemma emitter_counter_preserved_set_scratch:
  forall l n (target: temp_env) (v: val),
  emitter_layout_wf l n ->
  PTree.get (el_counter l) (PTree.set (el_scratch l) v target) =
    PTree.get (el_counter l) target.
Proof.
  intros l n target v WF. rewrite PTree.gso; auto.
  destruct WF as [? ? ? ? SC]. now apply not_eq_sym.
Qed.

(** Scalar emitter statements touch only the scratch, the declared source
    registers, and the loop counter.  This frame fact is used by the array
    compiler to keep its pointer parameter live across scalar instructions. *)
Definition emitter_outside_preserved (l: emitter_layout) (n: nat)
    (before after: temp_env) : Prop :=
  forall x,
    x <> el_scratch l ->
    x <> el_counter l ->
    (forall r, (r < n)%nat -> x <> el_reg l r) ->
    PTree.get x after = PTree.get x before.

Lemma exec_emitter_instr:
  forall fe ge en m l n idx idx_expr i source target source',
  emitter_layout_wf l n ->
  dinstr_wf n i ->
  typeof idx_expr = tulong ->
  emitter_regs_agree l n source target ->
  eval_e (genv_cenv ge) m target idx_expr =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_instr idx source i = Some source' ->
  exists target',
    exec_stmt_list fe ge en m target (emitter_instr l idx_expr i)
      target' Out_normal /\
    emitter_regs_agree l n source' target' /\
    PTree.get (el_counter l) target' = PTree.get (el_counter l) target /\
    emitter_outside_preserved l n target target'.
Proof.
  intros fe ge en m l n idx idx_expr i source target source'
    LWF IWF IDXT AG IDX RUN.
  destruct i as [dst src|dst op lhs rhs].
  - cbn [dinstr_wf eval_instr] in IWF, RUN.
    destruct IWF as [DST SWF].
    destruct (eval_operand idx source src) as [w|] eqn:E; try discriminate.
    inversion RUN; subst source'.
    set (target' := PTree.set (el_reg l dst) (Vlong w) target).
    exists target'. split.
    + cbn [emitter_instr]. econstructor.
      * apply exec_Sset. apply eval_e_sound.
        now apply (eval_e_emitter_operand (genv_cenv ge) m l n idx
          idx_expr source target src w SWF AG IDX E).
      * constructor.
    + repeat split.
      * unfold target'. now apply emitter_regs_agree_set.
      * unfold target'. now apply (emitter_counter_preserved_set_reg l n).
      * intros x XS XC XREG. unfold target'. rewrite PTree.gso.
        -- reflexivity.
        -- intro EQ. apply (XREG dst DST). exact EQ.
  - cbn [dinstr_wf eval_instr] in IWF, RUN.
    destruct IWF as [DST [LHSWF RHSWF]].
    destruct (eval_operand idx source lhs) as [a|] eqn:EL;
      try discriminate.
    destruct (eval_operand idx source rhs) as [b|] eqn:ER;
      try discriminate.
    destruct (eval_dop op a b) as [w|] eqn:OP; try discriminate.
    inversion RUN; subst source'.
    destruct (dop_is_comparison op) eqn:CMP.
    + destruct (eval_e_emitter_comparison_narrow
        (genv_cenv ge) m l n idx idx_expr source target op lhs rhs a b w
        CMP LHSWF RHSWF IDXT AG IDX EL ER OP) as [i [NARROW WI]].
      set (target1 := PTree.set (el_scratch l) (Vint i) target).
      set (target' := PTree.set (el_reg l dst) (Vlong w) target1).
      assert (XNARROW : ClightBigstep.exec_stmt fe ge en target m
          (Sset (el_scratch l)
            (Ecast (emitter_binop_expr l idx_expr op lhs rhs) tuchar))
          E0 target1 m Out_normal).
      { unfold target1. apply exec_Sset. apply eval_e_sound. exact NARROW. }
      assert (XWIDEN : ClightBigstep.exec_stmt fe ge en target1 m
          (Sset (el_reg l dst)
            (Ecast (Etempvar (el_scratch l) tuchar) tulong))
          E0 target' m Out_normal).
      { unfold target'. apply exec_Sset. apply eval_e_sound.
        rewrite <- WI. apply eval_e_emitter_scratch_widen.
        unfold target1. now rewrite PTree.gss. }
      exists target'. split.
      * cbn [emitter_instr]. rewrite CMP. cbn.
        econstructor.
        -- exact XNARROW.
        -- econstructor.
           ++ exact XWIDEN.
           ++ constructor.
      * repeat split.
        -- unfold target', target1.
           apply emitter_regs_agree_set; auto.
           now apply emitter_regs_agree_set_scratch.
        -- unfold target', target1.
           rewrite (emitter_counter_preserved_set_reg l n) by auto.
           now rewrite (emitter_counter_preserved_set_scratch l n) by auto.
        -- intros x XS XC XREG. unfold target', target1.
           rewrite !PTree.gso.
           ++ reflexivity.
           ++ exact XS.
           ++ intro EQ. apply (XREG dst DST). exact EQ.
    + assert (ARITH := eval_e_emitter_arithmetic
        (genv_cenv ge) m l n idx idx_expr source target op lhs rhs a b w
        CMP LHSWF RHSWF IDXT AG IDX EL ER OP).
      set (target' := PTree.set (el_reg l dst) (Vlong w) target).
      assert (XARITH : ClightBigstep.exec_stmt fe ge en target m
          (Sset (el_reg l dst)
            (emitter_binop_expr l idx_expr op lhs rhs))
          E0 target' m Out_normal).
      { unfold target'. apply exec_Sset. apply eval_e_sound. exact ARITH. }
      exists target'. split.
      * cbn [emitter_instr]. rewrite CMP. cbn.
        econstructor.
        -- exact XARITH.
        -- constructor.
      * repeat split.
        -- unfold target'. now apply emitter_regs_agree_set.
        -- unfold target'. now apply (emitter_counter_preserved_set_reg l n).
        -- intros x XS XC XREG. unfold target'. rewrite PTree.gso.
           ++ reflexivity.
           ++ intro EQ. apply (XREG dst DST). exact EQ.
Qed.

Definition emitter_index_expr (l: emitter_layout) (idx: nat) (e: expr)
    : Prop :=
  e = Econst_long (Int64.repr (Z.of_nat idx)) tulong \/
  e = Etempvar (el_counter l) tulong.

Lemma exec_emitter_instrs:
  forall fe ge en m l n idx idx_expr is source target source',
  emitter_layout_wf l n ->
  Forall (dinstr_wf n) is ->
  typeof idx_expr = tulong ->
  emitter_index_expr l idx idx_expr ->
  emitter_regs_agree l n source target ->
  eval_e (genv_cenv ge) m target idx_expr =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_instrs idx is source = Some source' ->
  exists target',
    exec_stmt_list fe ge en m target (emitter_instrs l idx_expr is)
      target' Out_normal /\
    emitter_regs_agree l n source' target' /\
    PTree.get (el_counter l) target' = PTree.get (el_counter l) target /\
    emitter_outside_preserved l n target target'.
Proof.
  intros fe ge en m l n idx idx_expr is.
  induction is as [|i is IH];
    intros source target source' LWF WF IDXT IDXS AG IDX RUN;
      cbn in RUN |- *.
  - inversion RUN; subst. eexists; repeat split; eauto using exec_stmt_list_nil.
  - inversion WF as [|? ? IWF REST]; subst.
    destruct (eval_instr idx source i) as [source1|] eqn:STEP;
      try discriminate.
    destruct (exec_emitter_instr fe ge en m l n idx idx_expr i
      source target source1 LWF IWF IDXT AG IDX STEP)
      as [target1 [X1 [AG1 [KEEP1 FRAME1]]]].
    assert (IDX1 : eval_e (genv_cenv ge) m target1 idx_expr =
        Some (Vlong (Int64.repr (Z.of_nat idx)))).
    { destruct IDXS as [STATIC|DYNAMIC].
      - subst idx_expr. reflexivity.
      - subst idx_expr. cbn [eval_e num_val] in IDX |- *.
        now rewrite KEEP1.
    }
    destruct (IH source1 target1 source' LWF REST IDXT IDXS AG1 IDX1 RUN)
      as [target' [XREST [AG' [KEEP' FRAME']]]].
    exists target'. split.
    + now apply exec_stmt_list_app_normal with (mid := target1).
    + repeat split.
      * exact AG'.
      * now rewrite KEEP', KEEP1.
      * intros x XS XC XREG. rewrite (FRAME' x XS XC XREG).
        exact (FRAME1 x XS XC XREG).
Qed.

(* -------------------------------------------------------------------- *)
(* Counter expressions and the exact [Swhile] loop. *)

Lemma eval_e_emitter_counter:
  forall ce m l target idx,
  PTree.get (el_counter l) target =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_e ce m target (Etempvar (el_counter l) tulong) =
    Some (Vlong (Int64.repr (Z.of_nat idx))).
Proof.
  intros ce m l target idx GET. cbn [eval_e num_val]. now rewrite GET.
Qed.

Lemma emitter_test_true:
  forall ge en m le l idx limit loop_limit,
  PTree.get (el_counter l) le =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  (idx < limit)%nat ->
  Z.of_nat limit < Int64.modulus ->
  loop_limit = Z.of_nat limit ->
  eval_expr ge en le m (emitter_test l loop_limit) (Vint Int.one) /\
  bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros ge en m le l idx limit loop_limit IDX LT FIT LIMIT.
  assert (RANGEI : 0 <= Z.of_nat idx <= Int64.max_unsigned).
  { unfold Int64.max_unsigned. lia. }
  assert (RANGEL : 0 <= Z.of_nat limit <= Int64.max_unsigned).
  { unfold Int64.max_unsigned. lia. }
  split; [|reflexivity]. subst loop_limit.
  unfold emitter_test.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr (Z.of_nat idx)))
    (v2 := Vlong (Int64.repr (Z.of_nat limit))).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop Int64.cmpu Val.of_bool Vtrue Vfalse].
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by assumption.
    destruct (zlt (Z.of_nat idx) (Z.of_nat limit)); [reflexivity|lia].
Qed.

Lemma emitter_test_false:
  forall ge en m le l limit loop_limit,
  PTree.get (el_counter l) le =
    Some (Vlong (Int64.repr (Z.of_nat limit))) ->
  Z.of_nat limit < Int64.modulus ->
  loop_limit = Z.of_nat limit ->
  eval_expr ge en le m (emitter_test l loop_limit) (Vint Int.zero) /\
  bool_val (Vint Int.zero) tint m = Some false.
Proof.
  intros ge en m le l limit loop_limit IDX FIT LIMIT.
  assert (RANGE : 0 <= Z.of_nat limit <= Int64.max_unsigned).
  { unfold Int64.max_unsigned. lia. }
  split; [|reflexivity]. subst loop_limit.
  unfold emitter_test.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr (Z.of_nat limit)))
    (v2 := Vlong (Int64.repr (Z.of_nat limit))).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop Int64.cmpu Val.of_bool Vtrue Vfalse].
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by assumption.
    destruct (zlt (Z.of_nat limit) (Z.of_nat limit)); [lia|reflexivity].
Qed.

Lemma emitter_increment_correct:
  forall fe ge en m l target idx,
  PTree.get (el_counter l) target =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  ClightBigstep.exec_stmt fe ge en target m (emitter_increment l) E0
    (PTree.set (el_counter l)
      (Vlong (Int64.repr (Z.of_nat (S idx)))) target)
    m Out_normal.
Proof.
  intros fe ge en m l target idx IDX. unfold emitter_increment.
  apply exec_Sset.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr (Z.of_nat idx)))
    (v2 := Vlong (Int64.repr 1)).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop]. f_equal. f_equal.
    unfold Int64.add. apply Int64.eqm_samerepr.
    rewrite Nat2Z.inj_succ. apply Int64.eqm_add.
    + apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
    + apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
Qed.

Theorem compile_emitter_loop_correct:
  forall fe ge en m l n limit loop_limit body start count
      source target source',
  emitter_layout_wf l n ->
  Forall (dinstr_wf n) body ->
  Z.of_nat limit < Int64.modulus ->
  loop_limit = Z.of_nat limit ->
  (start + count = limit)%nat ->
  emitter_regs_agree l n source target ->
  PTree.get (el_counter l) target =
    Some (Vlong (Int64.repr (Z.of_nat start))) ->
  eval_loop start count body source = Some source' ->
  exists target',
    ClightBigstep.exec_stmt fe ge en target m
      (emitter_loop l loop_limit body) E0 target' m Out_normal /\
    emitter_regs_agree l n source' target' /\
    PTree.get (el_counter l) target' =
      Some (Vlong (Int64.repr (Z.of_nat limit))).
Proof.
  intros fe ge en m l n limit loop_limit body start count.
  revert start.
  induction count as [|count IH];
    intros start source target source' LWF WF FIT LIMIT SUM AG IDX LOOP.
  - cbn in LOOP. inversion LOOP; subst source'.
    assert (EQ : start = limit) by lia. subst start.
    destruct (emitter_test_false ge en m target l limit loop_limit
      IDX FIT LIMIT) as [TEST BOOL].
    exists target. split.
    + unfold emitter_loop, Swhile.
      eapply exec_Sloop_stop1.
      * eapply exec_Sseq_2.
        -- eapply exec_Sifthenelse with
            (v1 := Vint Int.zero) (b := false).
           ++ exact TEST.
           ++ exact BOOL.
           ++ apply exec_Sbreak.
        -- discriminate.
      * apply Out_break_or_return_B.
    + auto.
  - cbn in LOOP.
    destruct (eval_instrs start body source) as [source1|] eqn:BODY;
      try discriminate.
    assert (IDXE : eval_e (genv_cenv ge) m target
        (Etempvar (el_counter l) tulong) =
        Some (Vlong (Int64.repr (Z.of_nat start)))).
    { now apply eval_e_emitter_counter. }
    destruct (exec_emitter_instrs fe ge en m l n start
      (Etempvar (el_counter l) tulong) body source target source1
      LWF WF eq_refl (or_intror eq_refl) AG IDXE BODY)
      as [target1 [XBODY [AG1 [KEEP _FRAME_BODY]]]].
    assert (IDX1 : PTree.get (el_counter l) target1 =
        Some (Vlong (Int64.repr (Z.of_nat start)))).
    { now rewrite KEEP. }
    set (target2 := PTree.set (el_counter l)
      (Vlong (Int64.repr (Z.of_nat (S start)))) target1).
    assert (XINC : ClightBigstep.exec_stmt fe ge en target1 m
        (emitter_increment l) E0 target2 m Out_normal).
    { unfold target2. now apply emitter_increment_correct. }
    assert (XINCLIST : exec_stmt_list fe ge en m target1
        [emitter_increment l] target2 Out_normal).
    { econstructor; [exact XINC|constructor]. }
    assert (XLOOPBODY : ClightBigstep.exec_stmt fe ge en target m
        (emitter_loop_body l body) E0 target2 m Out_normal).
    { unfold emitter_loop_body. apply exec_stmt_list_sequence.
      now apply exec_stmt_list_app_normal with (mid := target1). }
    assert (AG2 : emitter_regs_agree l n source1 target2).
    { unfold target2. now apply emitter_regs_agree_set_counter. }
    assert (IDX2 : PTree.get (el_counter l) target2 =
        Some (Vlong (Int64.repr (Z.of_nat (S start))))).
    { unfold target2. now rewrite PTree.gss. }
    assert (LT : (start < limit)%nat) by lia.
    destruct (emitter_test_true ge en m target l start limit loop_limit
      IDX LT FIT LIMIT) as [TEST BOOL].
    destruct (IH (S start) source1 target2 source' LWF WF FIT LIMIT
      ltac:(lia) AG2 IDX2 LOOP) as [target' [REST [AG' IDX']]].
    exists target'. split.
    + unfold emitter_loop, Swhile in REST |- *.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop.
      * change E0 with (E0 ** E0).
        eapply exec_Sseq_1.
        -- eapply exec_Sifthenelse with
             (v1 := Vint Int.one) (b := true).
           ++ exact TEST.
           ++ exact BOOL.
           ++ apply exec_Sskip.
        -- exact XLOOPBODY.
      * apply Out_normal_or_continue_N.
      * apply exec_Sskip.
      * exact REST.
    + auto.
Qed.

(* -------------------------------------------------------------------- *)
(* Whole exact emitter body and function call. *)

Lemma compile_emitted_rolled_body_correct:
  forall l loop_limit s p w fe ge en m,
  emitter_source_matches s p ->
  emitter_layout_wf l (es_reg_count s) ->
  rolled_wf p ->
  loop_limit = Z.of_nat (dp_loop_count p) ->
  dsl_denote p = Some w ->
  exists le',
    ClightBigstep.exec_stmt fe ge en
      (create_undef_temps
        (fn_temps (compile_emitted_rolled_program l loop_limit s))) m
      (fn_body (compile_emitted_rolled_program l loop_limit s))
      E0 le' m (Out_return (Some (Vlong w, tulong))).
Proof.
  intros l loop_limit s p w fe ge en m MATCH LAYOUT PWF LIMIT DEN.
  destruct MATCH as [MREG MINIT MBODY MEPI MOUT].
  assert (LWF : emitter_layout_wf l (dp_reg_count p)).
  { rewrite <- MREG. exact LAYOUT. }
  destruct PWF as [OUT INIT BODY EPI FIT].
  rewrite dsl_denote_structured in DEN.
  unfold structured_denote in DEN.
  destruct (eval_instrs 0 (preamble (dp_reg_count p) ++ dp_init p)
    (initial_temps p)) as [source1|] eqn:PREFIX; try discriminate.
  destruct (eval_loop 0 (dp_loop_count p) (dp_body p) source1)
    as [source2|] eqn:LOOP; try discriminate.
  destruct (eval_instrs 0 (dp_epilogue p) source2)
    as [source3|] eqn:EPILOGUE; try discriminate.
  destruct (PTree.get (reg_ident (dp_output p)) source3)
    as [v|] eqn:OUTPUT; try discriminate.
  destruct v; try discriminate. inversion DEN; subst i.

  set (target0 := create_undef_temps
    (fn_temps (compile_emitted_rolled_program l loop_limit s))).
  assert (AG0 : emitter_regs_agree l (dp_reg_count p)
      (initial_temps p) target0).
  { unfold target0, compile_emitted_rolled_program, initial_temps; cbn.
    now apply initial_emitter_regs_agree. }

  set (targetc := PTree.set (el_counter l) (Vlong Int64.zero) target0).
  assert (XCOUNTER : ClightBigstep.exec_stmt fe ge en target0 m
      (emitter_counter_zero l) E0 targetc m Out_normal).
  { unfold emitter_counter_zero, targetc. apply exec_Sset.
    apply eval_Econst_long. }
  assert (AGC : emitter_regs_agree l (dp_reg_count p)
      (initial_temps p) targetc).
  { unfold targetc. now apply emitter_regs_agree_set_counter. }

  set (targets := PTree.set (el_scratch l) (Vint Int.zero) targetc).
  assert (XSCRATCH : ClightBigstep.exec_stmt fe ge en targetc m
      (emitter_scratch_zero l) E0 targets m Out_normal).
  { unfold emitter_scratch_zero, targets. apply exec_Sset.
    apply eval_e_sound. reflexivity. }
  assert (AGS : emitter_regs_agree l (dp_reg_count p)
      (initial_temps p) targets).
  { unfold targets. now apply emitter_regs_agree_set_scratch. }
  assert (COUNTER0 : PTree.get (el_counter l) targets =
      Some (Vlong (Int64.repr (Z.of_nat 0)))).
  { unfold targets.
    rewrite (emitter_counter_preserved_set_scratch l (dp_reg_count p))
      by exact LWF.
    unfold targetc. now rewrite PTree.gss. }

  assert (PREFIX_WF : Forall (dinstr_wf (dp_reg_count p))
      (preamble (dp_reg_count p) ++ dp_init p)).
  { rewrite Forall_app. auto using preamble_wf. }
  assert (STATIC0 : eval_e (genv_cenv ge) m targets
      (Econst_long Int64.zero tulong) =
      Some (Vlong (Int64.repr (Z.of_nat 0)))) by reflexivity.
  destruct (exec_emitter_instrs fe ge en m l (dp_reg_count p) 0
      (Econst_long Int64.zero tulong)
      (preamble (dp_reg_count p) ++ dp_init p)
      (initial_temps p) targets source1 LWF PREFIX_WF eq_refl
      (or_introl eq_refl) AGS STATIC0 PREFIX)
    as [target1 [XPREFIX [AG1 [KEEP_PREFIX _FRAME_PREFIX]]]].
  assert (COUNTER1 : PTree.get (el_counter l) target1 =
      Some (Vlong (Int64.repr (Z.of_nat 0)))).
  { now rewrite KEEP_PREFIX. }

  destruct (compile_emitter_loop_correct fe ge en m l
      (dp_reg_count p) (dp_loop_count p) loop_limit (dp_body p)
      0 (dp_loop_count p) source1 target1 source2 LWF BODY FIT LIMIT
      ltac:(lia) AG1 COUNTER1 LOOP)
    as [target2 [XLOOP [AG2 COUNTER2]]].

  assert (STATIC_EPI : eval_e (genv_cenv ge) m target2
      (Econst_long Int64.zero tulong) =
      Some (Vlong (Int64.repr (Z.of_nat 0)))) by reflexivity.
  destruct (exec_emitter_instrs fe ge en m l (dp_reg_count p) 0
      (Econst_long Int64.zero tulong) (dp_epilogue p)
      source2 target2 source3 LWF EPI eq_refl (or_introl eq_refl)
      AG2 STATIC_EPI EPILOGUE)
    as [target3 [XEPI [AG3 [KEEP_EPI _FRAME_EPI]]]].
  assert (TOUTPUT : PTree.get (el_reg l (dp_output p)) target3 =
      Some (Vlong w)).
  { rewrite <- (AG3 (dp_output p) OUT). exact OUTPUT. }
  assert (XRETURN : ClightBigstep.exec_stmt fe ge en target3 m
      (Sreturn (Some (Etempvar (el_reg l (dp_output p)) tulong)))
      E0 target3 m (Out_return (Some (Vlong w, tulong)))).
  { apply exec_Sreturn_some. now apply eval_Etempvar. }

  assert (XCOUNTERS : exec_stmt_list fe ge en m target0
      [emitter_counter_zero l] targetc Out_normal).
  { econstructor; [exact XCOUNTER|constructor]. }
  assert (XSCRATCHS : exec_stmt_list fe ge en m targetc
      [emitter_scratch_zero l] targets Out_normal).
  { econstructor; [exact XSCRATCH|constructor]. }
  assert (XHEAD : exec_stmt_list fe ge en m target0
      [emitter_counter_zero l; emitter_scratch_zero l]
      targets Out_normal).
  { change [emitter_counter_zero l; emitter_scratch_zero l] with
      ([emitter_counter_zero l] ++ [emitter_scratch_zero l]).
    now apply exec_stmt_list_app_normal with (mid := targetc). }
  assert (XLOOPS : exec_stmt_list fe ge en m target1
      [emitter_loop l loop_limit (dp_body p)] target2 Out_normal).
  { econstructor; [exact XLOOP|constructor]. }
  assert (XRETURNS : exec_stmt_list fe ge en m target3
      [Sreturn (Some (Etempvar (el_reg l (dp_output p)) tulong))]
      target3 (Out_return (Some (Vlong w, tulong)))).
  { eapply exec_stmt_list_cons_abrupt; [exact XRETURN|discriminate]. }
  assert (XEPITAIL : exec_stmt_list fe ge en m target2
      (emitter_instrs l (Econst_long Int64.zero tulong) (dp_epilogue p) ++
       [Sreturn (Some (Etempvar (el_reg l (dp_output p)) tulong))])
      target3 (Out_return (Some (Vlong w, tulong)))).
  { now apply exec_stmt_list_app_normal with (mid := target3). }
  assert (XLOOPTAIL : exec_stmt_list fe ge en m target1
      ([emitter_loop l loop_limit (dp_body p)] ++
       emitter_instrs l (Econst_long Int64.zero tulong) (dp_epilogue p) ++
       [Sreturn (Some (Etempvar (el_reg l (dp_output p)) tulong))])
      target3 (Out_return (Some (Vlong w, tulong)))).
  { apply exec_stmt_list_app_normal with (mid := target2); auto. }
  assert (XPREFIXTAIL : exec_stmt_list fe ge en m targets
      (emitter_instrs l (Econst_long Int64.zero tulong)
         (preamble (dp_reg_count p) ++ dp_init p) ++
       [emitter_loop l loop_limit (dp_body p)] ++
       emitter_instrs l (Econst_long Int64.zero tulong) (dp_epilogue p) ++
       [Sreturn (Some (Etempvar (el_reg l (dp_output p)) tulong))])
      target3 (Out_return (Some (Vlong w, tulong)))).
  { apply exec_stmt_list_app_normal with (mid := target1); auto. }
  assert (XALL : exec_stmt_list fe ge en m target0
      (emitter_body_statements l loop_limit s) target3
      (Out_return (Some (Vlong w, tulong)))).
  { unfold emitter_body_statements.
    rewrite MREG, MINIT, MBODY, MEPI, MOUT.
    apply exec_stmt_list_app_normal with (mid := targets); auto. }

  exists target3.
  change (ClightBigstep.exec_stmt fe ge en target0 m
    (compile_emitted_rolled_body l loop_limit s) E0 target3 m
    (Out_return (Some (Vlong w, tulong)))).
  unfold compile_emitted_rolled_body.
  now apply exec_stmt_list_sequence.
Qed.

Theorem compile_emitted_rolled_program_correct:
  forall l loop_limit s p w ge m,
  emitter_source_matches s p ->
  emitter_layout_wf l (es_reg_count s) ->
  rolled_wf p ->
  loop_limit = Z.of_nat (dp_loop_count p) ->
  dsl_denote p = Some w ->
  ClightBigstep.eval_funcall function_entry2 ge m
    (Internal (compile_emitted_rolled_program l loop_limit s)) [] E0 m
    (Vlong w).
Proof.
  intros l loop_limit s p w ge m MATCH LWF PWF LIMIT DEN.
  destruct (compile_emitted_rolled_body_correct l loop_limit s p w
    function_entry2 ge empty_env m MATCH LWF PWF LIMIT DEN) as [le' BODY].
  eapply eval_funcall_internal with
    (e := empty_env)
    (le1 := create_undef_temps
      (fn_temps (compile_emitted_rolled_program l loop_limit s)))
    (le2 := le') (m1 := m) (m2 := m)
    (out := Out_return (Some (Vlong w, tulong))).
  - constructor.
    + constructor.
    + constructor.
    + red; simpl; tauto.
    + constructor.
    + reflexivity.
  - exact BODY.
  - simpl. split; [discriminate|reflexivity].
  - reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* Closed scalability regression.  The semantic program retains its count as
   [Z.to_nat] only behind an abstract [dsl_denote] hypothesis.  The exact AST
   compiler and its result carry the independent count-free source, so this
   proof never converts a trillion to unary [nat]. *)

Definition emitter_trillion_limit : Z := 1000000000000.

Definition emitter_trillion_source : emitter_source := {|
  es_reg_count := 1%nat;
  es_init := [];
  es_body := [];
  es_epilogue := [];
  es_output := 0%nat
|}.

Definition emitter_trillion_semantic : dsl_program := {|
  dp_reg_count := 1%nat;
  dp_loop_count := Z.to_nat emitter_trillion_limit;
  dp_init := [];
  dp_body := [];
  dp_epilogue := [];
  dp_output := 0%nat
|}.

Definition emitter_trillion_layout : emitter_layout := {|
  el_scratch := 1%positive;
  el_regs := [2%positive];
  el_counter := 3%positive
|}.

Lemma emitter_trillion_matches:
  emitter_source_matches emitter_trillion_source
    emitter_trillion_semantic.
Proof. constructor; reflexivity. Qed.

Lemma emitter_trillion_layout_wf:
  emitter_layout_wf emitter_trillion_layout
    (es_reg_count emitter_trillion_source).
Proof.
  constructor; cbn.
  - reflexivity.
  - constructor; [cbn; tauto|constructor].
  - intros [H|[]]; discriminate.
  - intros [H|[]]; discriminate.
  - discriminate.
Qed.

Lemma emitter_trillion_semantic_wf:
  rolled_wf emitter_trillion_semantic.
Proof.
  constructor.
  - cbn; lia.
  - constructor.
  - constructor.
  - constructor.
  - change
      (Z.of_nat (Z.to_nat 1000000000000) < Int64.modulus).
    rewrite Z2Nat.id by lia.
    change (1000000000000 < 18446744073709551616)%Z. lia.
Qed.

Lemma emitter_trillion_limit_matches:
  emitter_trillion_limit =
    Z.of_nat (dp_loop_count emitter_trillion_semantic).
Proof.
  change (1000000000000 = Z.of_nat (Z.to_nat 1000000000000)).
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

(** A manually written exact AST equality.  In particular, the guard contains
    the binary [Z] literal directly; neither side mentions the semantic
    program or its [Z.to_nat] loop count. *)
Example emitter_trillion_exact_ast:
  compile_emitted_rolled_program emitter_trillion_layout
    emitter_trillion_limit emitter_trillion_source = {|
      fn_return := tulong;
      fn_callconv := cc_default;
      fn_params := [];
      fn_vars := [];
      fn_temps :=
        [(1%positive, tuchar); (2%positive, tulong); (3%positive, tulong)];
      fn_body :=
        Ssequence
          (Sset 3%positive (Econst_long Int64.zero tulong))
          (Ssequence
            (Sset 1%positive (Ecast (Econst_int Int.zero tint) tuchar))
            (Ssequence
              (Sset 2%positive
                (Econst_long (Int64.repr 0) tulong))
              (Ssequence
                (Swhile
                  (Ebinop Olt (Etempvar 3%positive tulong)
                    (Econst_long (Int64.repr 1000000000000) tulong) tint)
                  (Sset 3%positive
                    (Ebinop Oadd (Etempvar 3%positive tulong)
                      (Econst_long (Int64.repr 1) tulong) tulong)))
                (Sreturn (Some (Etempvar 2%positive tulong))))))
    |}.
Proof. reflexivity. Qed.

Theorem emitter_trillion_exact_contract:
  forall w ge m,
  dsl_denote emitter_trillion_semantic = Some w ->
  ClightBigstep.eval_funcall function_entry2 ge m
    (Internal (compile_emitted_rolled_program emitter_trillion_layout
      emitter_trillion_limit emitter_trillion_source)) [] E0 m (Vlong w).
Proof.
  intros w ge m DEN.
  eapply compile_emitted_rolled_program_correct.
  - exact emitter_trillion_matches.
  - exact emitter_trillion_layout_wf.
  - exact emitter_trillion_semantic_wf.
  - exact emitter_trillion_limit_matches.
  - exact DEN.
Qed.

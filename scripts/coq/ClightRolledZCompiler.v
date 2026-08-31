(* A genuinely large-count-safe rolled compiler for the scalar certificate DSL.

   [ClightDSLCompiler.dsl_program] stores its loop count as a Coq [nat].  That
   is convenient for executable tests, but a closed count such as 10^12 can
   still expose an enormous Peano numeral when definitions are unfolded.  The
   source language below stores the loop limit as [Z] and gives the loop a
   relational semantics.  Consequently:

   - the source program and generated Clight AST contain the limit once, as a
     binary [Z] numeral;
   - the Clight program contains one [Sloop] and one copy of the body;
   - correctness is proved by induction on a semantic derivation, never by
     unrolling or normalising the closed loop limit; and
   - an external computation/attestation may supply the single proposition
     [zprogram_denotes p w], after which the generic theorem below produces
     CompCert [eval_funcall] evidence.

   This is the canonical Clight AST proved here.  Relating a separately printed
   C file and clightgen's parsed AST to this canonical AST remains a distinct
   emission-correspondence obligation. *)

From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightFragmentSem Direct.ClightDefinedOps.
Require Import Direct.ClightDSLCompiler.

Import ListNotations.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------- *)
(* Compact source syntax and relational loop semantics. *)

Record z_dsl_program : Type := {
  zdp_reg_count: nat;
  zdp_loop_limit: Z;
  zdp_init: list dinstr;
  zdp_body: list dinstr;
  zdp_epilogue: list dinstr;
  zdp_output: nat
}.

Definition zdoperand_wf (n: nat) (o: doperand) : Prop :=
  match o with
  | Dreg r => (r < n)%nat
  | Dlit _ | Didx => True
  end.

Definition zdinstr_wf (n: nat) (i: dinstr) : Prop :=
  match i with
  | Dmov dst src => (dst < n)%nat /\ zdoperand_wf n src
  | Dbinop dst _ lhs rhs =>
      (dst < n)%nat /\ zdoperand_wf n lhs /\ zdoperand_wf n rhs
  end.

Record zrolled_wf (p: z_dsl_program) : Prop := {
  zrw_output: (zdp_output p < zdp_reg_count p)%nat;
  zrw_init: Forall (zdinstr_wf (zdp_reg_count p)) (zdp_init p);
  zrw_body: Forall (zdinstr_wf (zdp_reg_count p)) (zdp_body p);
  zrw_epilogue: Forall (zdinstr_wf (zdp_reg_count p)) (zdp_epilogue p);
  zrw_limit_range: 0 <= zdp_loop_limit p < Int64.modulus
}.

Definition zidx_ident (n: nat) : ident := reg_ident n.

Definition eval_zoperand (idx: Z) (le: temp_env) (o: doperand)
    : option int64 :=
  match o with
  | Dreg r =>
      match PTree.get (reg_ident r) le with
      | Some (Vlong w) => Some w
      | _ => None
      end
  | Dlit z => Some (Int64.repr z)
  | Didx => Some (Int64.repr idx)
  end.

Definition eval_zinstr (idx: Z) (le: temp_env) (i: dinstr)
    : option temp_env :=
  match i with
  | Dmov dst src =>
      match eval_zoperand idx le src with
      | Some w => Some (PTree.set (reg_ident dst) (Vlong w) le)
      | None => None
      end
  | Dbinop dst op lhs rhs =>
      match eval_zoperand idx le lhs, eval_zoperand idx le rhs with
      | Some a, Some b =>
          match eval_dop op a b with
          | Some w => Some (PTree.set (reg_ident dst) (Vlong w) le)
          | None => None
          end
      | _, _ => None
      end
  end.

Fixpoint eval_zinstrs (idx: Z) (is: list dinstr) (le: temp_env)
    : option temp_env :=
  match is with
  | [] => Some le
  | i :: rest =>
      match eval_zinstr idx le i with
      | Some le' => eval_zinstrs idx rest le'
      | None => None
      end
  end.

(** [zeval_loop n body limit idx le le'] says that executing [body] for the
    half-open index interval [[idx, limit)] transforms [le] into [le'].
    The relation is intentionally not a recursive function on [limit].  A
    receipt can assert one instance regardless of how large [limit] is. *)
Inductive zeval_loop (n: nat) (body: list dinstr) (limit: Z)
    : Z -> temp_env -> temp_env -> Prop :=
  | zeval_loop_done : forall le,
      zeval_loop n body limit limit le le
  | zeval_loop_step : forall idx le mid out,
      0 <= idx < limit ->
      eval_zinstrs idx body le = Some mid ->
      zeval_loop n body limit (idx + 1)
        (PTree.set (zidx_ident n) (Vlong (Int64.repr (idx + 1))) mid) out ->
      zeval_loop n body limit idx le out.

Definition zrolled_temp_decls (n: nat) : list (ident * type) :=
  (zidx_ident n, tulong) :: temp_decls n.

Definition zinitial_temps (p: z_dsl_program) : temp_env :=
  create_undef_temps (zrolled_temp_decls (zdp_reg_count p)).

(** Relational denotation used as the compact boundary for an externally
    computed result.  Prefix and epilogue are finite straight-line programs;
    only the potentially huge loop is relational. *)
Inductive zprogram_denotes (p: z_dsl_program) (w: int64) : Prop :=
  | zprogram_denotes_intro : forall le1 le2 le3,
      eval_instrs 0 (preamble (zdp_reg_count p) ++ zdp_init p)
        (zinitial_temps p) = Some le1 ->
      zeval_loop (zdp_reg_count p) (zdp_body p) (zdp_loop_limit p) 0
        (PTree.set (zidx_ident (zdp_reg_count p)) (Vlong Int64.zero) le1)
        le2 ->
      eval_instrs 0 (zdp_epilogue p) le2 = Some le3 ->
      PTree.get (reg_ident (zdp_output p)) le3 = Some (Vlong w) ->
      zprogram_denotes p w.

(* -------------------------------------------------------------------- *)
(* One-loop canonical Clight compiler. *)

Definition compile_zoperand (n: nat) (o: doperand) : expr :=
  match o with
  | Dreg r => Etempvar (reg_ident r) tulong
  | Dlit z => Econst_long (Int64.repr z) tulong
  | Didx => Etempvar (zidx_ident n) tulong
  end.

Definition compile_zrhs (n: nat) (op: dop)
    (lhs rhs: doperand) : expr :=
  Ecast
    (Ebinop (cop_of_dop op) (compile_zoperand n lhs)
      (compile_zoperand n rhs) (dop_result_type op))
    tulong.

Definition compile_zinstr (n: nat) (i: dinstr) : statement :=
  match i with
  | Dmov dst src => Sset (reg_ident dst) (compile_zoperand n src)
  | Dbinop dst op lhs rhs =>
      Sset (reg_ident dst) (compile_zrhs n op lhs rhs)
  end.

Fixpoint compile_zinstrs (n: nat) (is: list dinstr) : statement :=
  match is with
  | [] => Sskip
  | i :: rest =>
      Ssequence (compile_zinstr n i) (compile_zinstrs n rest)
  end.

Fixpoint compile_zstatic_instrs (idx: nat) (is: list dinstr) : statement :=
  match is with
  | [] => Sskip
  | i :: rest =>
      Ssequence (compile_instr idx i) (compile_zstatic_instrs idx rest)
  end.

Definition zrolled_test (n: nat) (limit: Z) : expr :=
  Ebinop Olt
    (Etempvar (zidx_ident n) tulong)
    (Econst_long (Int64.repr limit) tulong)
    tint.

Definition zrolled_increment (n: nat) : statement :=
  Sset (zidx_ident n)
    (Ebinop Oadd
      (Etempvar (zidx_ident n) tulong)
      (Econst_long (Int64.repr 1) tulong)
      tulong).

Definition compile_zrolled_loop (n: nat) (limit: Z)
    (body: list dinstr) : statement :=
  Sloop
    (Sifthenelse (zrolled_test n limit)
      (compile_zinstrs n body) Sbreak)
    (zrolled_increment n).

Definition compile_zrolled_body (p: z_dsl_program) : statement :=
  Ssequence
    (compile_zstatic_instrs 0
      (preamble (zdp_reg_count p) ++ zdp_init p))
    (Ssequence
      (Sset (zidx_ident (zdp_reg_count p))
        (Econst_long Int64.zero tulong))
      (Ssequence
        (compile_zrolled_loop (zdp_reg_count p) (zdp_loop_limit p)
          (zdp_body p))
        (Ssequence
          (compile_zstatic_instrs 0 (zdp_epilogue p))
          (Sreturn
            (Some (Etempvar (reg_ident (zdp_output p)) tulong)))))).

Definition compile_zrolled_program (p: z_dsl_program) : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := [];
  fn_vars := [];
  fn_temps := zrolled_temp_decls (zdp_reg_count p);
  fn_body := compile_zrolled_body p
|}.

(* -------------------------------------------------------------------- *)
(* Straight-line correctness and preservation of the fresh counter. *)

Lemma zreg_ident_inj:
  forall r s, reg_ident r = reg_ident s -> r = s.
Proof.
  intros r s H. exact (SuccNat2Pos.inj r s H).
Qed.

Lemma zreg_ident_fresh:
  forall r n, (r < n)%nat -> reg_ident r <> zidx_ident n.
Proof.
  intros r n LT EQ. apply zreg_ident_inj in EQ. lia.
Qed.

Lemma eval_zinstr_preserves_idx:
  forall n idx i le le',
  zdinstr_wf n i ->
  eval_zinstr idx le i = Some le' ->
  PTree.get (zidx_ident n) le' = PTree.get (zidx_ident n) le.
Proof.
  intros n idx i le le' WF RUN.
  destruct i as [dst src|dst op lhs rhs]; cbn in WF, RUN.
  - destruct WF as [DST _].
    destruct (eval_zoperand idx le src) as [w|]; try discriminate.
    inversion RUN; subst. rewrite PTree.gso; auto.
    now apply not_eq_sym, zreg_ident_fresh.
  - destruct WF as [DST _].
    destruct (eval_zoperand idx le lhs) as [a|]; try discriminate.
    destruct (eval_zoperand idx le rhs) as [b|]; try discriminate.
    destruct (eval_dop op a b) as [w|]; try discriminate.
    inversion RUN; subst. rewrite PTree.gso; auto.
    now apply not_eq_sym, zreg_ident_fresh.
Qed.

Lemma eval_zinstrs_preserves_idx:
  forall n idx is le le',
  Forall (zdinstr_wf n) is ->
  eval_zinstrs idx is le = Some le' ->
  PTree.get (zidx_ident n) le' = PTree.get (zidx_ident n) le.
Proof.
  intros n idx is; induction is as [|i is IH];
    intros le le' WF RUN; cbn in RUN.
  - inversion RUN; reflexivity.
  - inversion WF as [|? ? IWF REST]; subst.
    destruct (eval_zinstr idx le i) as [le1|] eqn:STEP; try discriminate.
    rewrite (IH le1 le' REST RUN).
    now apply (eval_zinstr_preserves_idx n idx i le le1 IWF STEP).
Qed.

Lemma run_compile_zstatic_instrs:
  forall ce m idx is le le',
  eval_instrs idx is le = Some le' ->
  run ce m (compile_zstatic_instrs idx is) le =
    Some (le', Out_normal).
Proof.
  intros ce m idx is; induction is as [|i is IH];
    intros le le' RUN; cbn in RUN |- *.
  - inversion RUN; reflexivity.
  - destruct (eval_instr idx le i) as [le1|] eqn:STEP; try discriminate.
    rewrite (run_compile_instr ce m idx le i le1 STEP).
    exact (IH le1 le' RUN).
Qed.

Lemma typeof_compile_zoperand:
  forall n o, typeof (compile_zoperand n o) = tulong.
Proof. intros n o; destruct o; reflexivity. Qed.

Lemma eval_e_compile_zoperand:
  forall ce m n idx le o w,
  PTree.get (zidx_ident n) le = Some (Vlong (Int64.repr idx)) ->
  eval_zoperand idx le o = Some w ->
  eval_e ce m le (compile_zoperand n o) = Some (Vlong w).
Proof.
  intros ce m n idx le o w IDX EVAL.
  destruct o; cbn in EVAL |- *.
  - destruct (PTree.get (reg_ident r) le) as [v|] eqn:G;
      try discriminate.
    destruct v; try discriminate. inversion EVAL; subst; reflexivity.
  - inversion EVAL; reflexivity.
  - rewrite IDX. inversion EVAL; reflexivity.
Qed.

Lemma eval_e_compile_zrhs:
  forall ce m n idx le op lhs rhs a b w,
  PTree.get (zidx_ident n) le = Some (Vlong (Int64.repr idx)) ->
  eval_zoperand idx le lhs = Some a ->
  eval_zoperand idx le rhs = Some b ->
  eval_dop op a b = Some w ->
  eval_e ce m le (compile_zrhs n op lhs rhs) = Some (Vlong w).
Proof.
  intros ce m n idx le op lhs rhs a b w IDX HL HR HOP.
  unfold compile_zrhs; cbn.
  rewrite (eval_e_compile_zoperand ce m n idx le lhs a IDX HL).
  rewrite (eval_e_compile_zoperand ce m n idx le rhs b IDX HR).
  rewrite !typeof_compile_zoperand.
  assert (BOK : binop_ok (cop_of_dop op) tulong tulong = true)
    by (destruct op; reflexivity).
  rewrite BOK, sem_binary_operation_u64_exact.
  unfold eval_dop in HOP.
  destruct op;
    cbn [cop_of_dop dop_result_type eval_u64_binop val_u64
      Int64.cmpu Val.of_bool Vtrue Vfalse sem_cast classify_cast
      cast_int_long] in HOP |- *;
    unfold Val.of_bool in HOP |- *;
    repeat match goal with
    | H : context [if ?c then _ else _] |- _ => destruct c eqn:?
    | |- context [if ?c then _ else _] => destruct c eqn:?
    end;
    try discriminate;
    inversion HOP; subst; reflexivity.
Qed.

Lemma run_compile_zinstr:
  forall ce m n idx le i le',
  PTree.get (zidx_ident n) le = Some (Vlong (Int64.repr idx)) ->
  eval_zinstr idx le i = Some le' ->
  run ce m (compile_zinstr n i) le = Some (le', Out_normal).
Proof.
  intros ce m n idx le i le' IDX RUN.
  destruct i as [dst src|dst op lhs rhs].
  - cbn [eval_zinstr] in RUN.
    destruct (eval_zoperand idx le src) as [w|] eqn:E; try discriminate.
    inversion RUN; subst.
    change
      (match eval_e ce m le (compile_zoperand n src) with
       | Some v => Some (PTree.set (reg_ident dst) v le, Out_normal)
       | None => None
       end = Some (PTree.set (reg_ident dst) (Vlong w) le, Out_normal)).
    now rewrite (eval_e_compile_zoperand ce m n idx le src w IDX E).
  - cbn [eval_zinstr] in RUN.
    destruct (eval_zoperand idx le lhs) as [a|] eqn:EL; try discriminate.
    destruct (eval_zoperand idx le rhs) as [b|] eqn:ER; try discriminate.
    destruct (eval_dop op a b) as [w|] eqn:EO; try discriminate.
    inversion RUN; subst.
    change
      (match eval_e ce m le (compile_zrhs n op lhs rhs) with
       | Some v => Some (PTree.set (reg_ident dst) v le, Out_normal)
       | None => None
       end = Some (PTree.set (reg_ident dst) (Vlong w) le, Out_normal)).
    now rewrite
      (eval_e_compile_zrhs ce m n idx le op lhs rhs a b w IDX EL ER EO).
Qed.

Lemma run_compile_zinstrs:
  forall ce m n idx is le le',
  Forall (zdinstr_wf n) is ->
  PTree.get (zidx_ident n) le = Some (Vlong (Int64.repr idx)) ->
  eval_zinstrs idx is le = Some le' ->
  run ce m (compile_zinstrs n is) le = Some (le', Out_normal) /\
  PTree.get (zidx_ident n) le' = Some (Vlong (Int64.repr idx)).
Proof.
  intros ce m n idx is; induction is as [|i is IH];
    intros le le' WF IDX RUN; cbn in RUN |- *.
  - inversion RUN; subst; auto.
  - inversion WF as [|? ? IWF REST]; subst.
    destruct (eval_zinstr idx le i) as [le1|] eqn:STEP; try discriminate.
    rewrite (run_compile_zinstr ce m n idx le i le1 IDX STEP).
    assert (IDX1 : PTree.get (zidx_ident n) le1 =
        Some (Vlong (Int64.repr idx))).
    { rewrite (eval_zinstr_preserves_idx n idx i le le1 IWF STEP). exact IDX. }
    exact (IH le1 le' REST IDX1 RUN).
Qed.

(* -------------------------------------------------------------------- *)
(* The relational loop is simulated by the single Clight [Sloop]. *)

Lemma zrolled_test_true:
  forall ge en m le n idx limit,
  PTree.get (zidx_ident n) le = Some (Vlong (Int64.repr idx)) ->
  0 <= idx < limit ->
  limit < Int64.modulus ->
  eval_expr ge en le m (zrolled_test n limit) (Vint Int.one) /\
  bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros ge en m le n idx limit IDX RANGE FIT.
  assert (RANGEI : 0 <= idx < Int64.modulus) by lia.
  assert (RANGEL : 0 <= limit < Int64.modulus) by lia.
  split; [|reflexivity].
  unfold zrolled_test.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr idx))
    (v2 := Vlong (Int64.repr limit)).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop Int64.cmpu Int64.ltu Val.of_bool Vtrue Vfalse].
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
    destruct (zlt idx limit); [reflexivity|lia].
Qed.

Lemma zrolled_test_false:
  forall ge en m le n limit,
  PTree.get (zidx_ident n) le = Some (Vlong (Int64.repr limit)) ->
  0 <= limit < Int64.modulus ->
  eval_expr ge en le m (zrolled_test n limit) (Vint Int.zero) /\
  bool_val (Vint Int.zero) tint m = Some false.
Proof.
  intros ge en m le n limit IDX RANGE.
  split; [|reflexivity].
  unfold zrolled_test.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr limit))
    (v2 := Vlong (Int64.repr limit)).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop Int64.cmpu Int64.ltu Val.of_bool Vtrue Vfalse].
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
    destruct (zlt limit limit); [lia|reflexivity].
Qed.

Lemma zrolled_increment_expr:
  forall ge en m le n idx,
  PTree.get (zidx_ident n) le = Some (Vlong (Int64.repr idx)) ->
  eval_expr ge en le m
    (Ebinop Oadd
      (Etempvar (zidx_ident n) tulong)
      (Econst_long (Int64.repr 1) tulong) tulong)
    (Vlong (Int64.repr (idx + 1))).
Proof.
  intros ge en m le n idx IDX.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr idx))
    (v2 := Vlong (Int64.repr 1)).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop]. f_equal. f_equal.
    unfold Int64.add.
    apply Int64.eqm_samerepr.
    apply Int64.eqm_add.
    + apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
    + apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
Qed.

Theorem compile_zrolled_loop_correct:
  forall fe ge en m n body limit idx le out,
  Forall (zdinstr_wf n) body ->
  0 <= limit < Int64.modulus ->
  PTree.get (zidx_ident n) le = Some (Vlong (Int64.repr idx)) ->
  zeval_loop n body limit idx le out ->
  ClightBigstep.exec_stmt fe ge en le m
    (compile_zrolled_loop n limit body) E0 out m Out_normal.
Proof.
  intros fe ge en m n body limit idx le out WF LIMIT IDX LOOP.
  induction LOOP as
      [done_le
      |step_idx step_le mid step_out RANGE BODY REST IH].
  - destruct (zrolled_test_false ge en m done_le n limit IDX LIMIT)
      as [TEST BOOL].
    unfold compile_zrolled_loop.
    eapply exec_Sloop_stop1.
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      * exact TEST.
      * exact BOOL.
      * apply exec_Sbreak.
    + apply Out_break_or_return_B.
  - destruct (run_compile_zinstrs (genv_cenv ge) m n step_idx body
      step_le mid WF IDX BODY) as [RUNBODY IDXMID].
    destruct (zrolled_test_true ge en m step_le n step_idx limit
      IDX RANGE (proj2 LIMIT)) as [TEST BOOL].
    assert (INCR : ClightBigstep.exec_stmt fe ge en mid m
        (zrolled_increment n) E0
        (PTree.set (zidx_ident n)
          (Vlong (Int64.repr (step_idx + 1))) mid)
        m Out_normal).
    { unfold zrolled_increment. apply exec_Sset.
      now apply zrolled_increment_expr. }
    assert (IDXNEXT :
      PTree.get (zidx_ident n)
        (PTree.set (zidx_ident n)
          (Vlong (Int64.repr (step_idx + 1))) mid) =
      Some (Vlong (Int64.repr (step_idx + 1)))).
    { now rewrite PTree.gss. }
    specialize (IH IDXNEXT).
    unfold compile_zrolled_loop in IH |- *.
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop.
    + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
      * exact TEST.
      * exact BOOL.
      * eapply run_sound. exact RUNBODY.
    + apply Out_normal_or_continue_N.
    + exact INCR.
    + exact IH.
Qed.

(* -------------------------------------------------------------------- *)
(* End-to-end generic function theorem. *)

Lemma compile_zrolled_body_correct:
  forall p w fe ge en m,
  zrolled_wf p ->
  zprogram_denotes p w ->
  exists le',
    ClightBigstep.exec_stmt fe ge en
      (create_undef_temps (fn_temps (compile_zrolled_program p))) m
      (fn_body (compile_zrolled_program p)) E0 le' m
      (Out_return (Some (Vlong w, tulong))).
Proof.
  intros p w fe ge en m WF DEN.
  destruct WF as [OUT INIT BODY EPI LIMIT].
  inversion DEN as [le1 le2 le3 PREFIX LOOP EPILOGUE OUTPUT]; subst.
  set (target0 := create_undef_temps
    (fn_temps (compile_zrolled_program p))).
  assert (XPREFIX : ClightBigstep.exec_stmt fe ge en target0 m
      (compile_zstatic_instrs 0
        (preamble (zdp_reg_count p) ++ zdp_init p))
      E0 le1 m Out_normal).
  { apply run_sound.
    unfold target0, compile_zrolled_program, zinitial_temps in PREFIX; cbn in *.
    now apply run_compile_zstatic_instrs. }

  set (le1i := PTree.set (zidx_ident (zdp_reg_count p))
    (Vlong Int64.zero) le1).
  assert (XINIT : ClightBigstep.exec_stmt fe ge en le1 m
      (Sset (zidx_ident (zdp_reg_count p))
        (Econst_long Int64.zero tulong)) E0 le1i m Out_normal).
  { unfold le1i. apply exec_Sset. constructor. }
  assert (IDX0 : PTree.get (zidx_ident (zdp_reg_count p)) le1i =
      Some (Vlong (Int64.repr 0))).
  { unfold le1i. rewrite PTree.gss. reflexivity. }
  assert (LOOP' : zeval_loop (zdp_reg_count p) (zdp_body p)
      (zdp_loop_limit p) 0 le1i le2).
  { unfold le1i. exact LOOP. }
  assert (XLOOP : ClightBigstep.exec_stmt fe ge en le1i m
      (compile_zrolled_loop (zdp_reg_count p) (zdp_loop_limit p)
        (zdp_body p)) E0 le2 m Out_normal).
  { eapply compile_zrolled_loop_correct; eauto. }

  assert (XEPI : ClightBigstep.exec_stmt fe ge en le2 m
      (compile_zstatic_instrs 0 (zdp_epilogue p))
      E0 le3 m Out_normal).
  { apply run_sound. now apply run_compile_zstatic_instrs. }
  assert (XRETURN : ClightBigstep.exec_stmt fe ge en le3 m
      (Sreturn (Some (Etempvar (reg_ident (zdp_output p)) tulong)))
      E0 le3 m (Out_return (Some (Vlong w, tulong)))).
  { apply exec_Sreturn_some. now apply eval_Etempvar. }

  exists le3.
  unfold compile_zrolled_program, compile_zrolled_body; cbn.
  change E0 with (E0 ** (E0 ** (E0 ** (E0 ** E0)))).
  eapply exec_Sseq_1; [exact XPREFIX|].
  eapply exec_Sseq_1; [exact XINIT|].
  eapply exec_Sseq_1; [exact XLOOP|].
  eapply exec_Sseq_1; [exact XEPI|exact XRETURN].
Qed.

Theorem compile_zrolled_program_correct:
  forall p w ge m,
  zrolled_wf p ->
  zprogram_denotes p w ->
  ClightBigstep.eval_funcall function_entry2 ge m
    (Internal (compile_zrolled_program p)) [] E0 m (Vlong w).
Proof.
  intros p w ge m WF DEN.
  destruct (compile_zrolled_body_correct p w function_entry2 ge empty_env m
    WF DEN) as [le' BODY].
  eapply eval_funcall_internal with
    (e := empty_env)
    (le1 := create_undef_temps (fn_temps (compile_zrolled_program p)))
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
(* Closed trillion-iteration contract: elaboration remains small and quick. *)

Definition trillion_limit : Z := 1000000000000.

Definition trillion_program : z_dsl_program := {|
  zdp_reg_count := 1%nat;
  zdp_loop_limit := trillion_limit;
  zdp_init := [Dmov 0%nat (Dlit 0)];
  zdp_body := [Dbinop 0%nat Dadd (Dreg 0%nat) (Dlit 1)];
  zdp_epilogue := [];
  zdp_output := 0%nat
|}.

Lemma trillion_program_wf : zrolled_wf trillion_program.
Proof.
  constructor.
  - exact (Nat.lt_0_succ 0).
  - cbn [trillion_program zdinstr_wf zdoperand_wf].
    repeat constructor; lia.
  - cbn [trillion_program zdinstr_wf zdoperand_wf].
    repeat constructor; lia.
  - cbn [trillion_program]. constructor.
  - change (0 <= 1000000000000 < 18446744073709551616)%Z.
    lia.
Qed.

(** The literal occurs directly in the compact AST.  This proof is
    definitional and does not compute a trillion iterations (or even convert
    the numeral to [nat]). *)
Example trillion_limit_emitted_directly :
  zrolled_test 1%nat (zdp_loop_limit trillion_program) =
    Ebinop Olt
      (Etempvar (zidx_ident 1%nat) tulong)
      (Econst_long (Int64.repr 1000000000000) tulong)
      tint.
Proof. reflexivity. Qed.

(** This is the receipt-to-CompCert theorem a generated contract uses.  Its
    premise may later be discharged by the attestation axiom. *)
Theorem trillion_program_contract:
  forall w ge m,
  zprogram_denotes trillion_program w ->
  ClightBigstep.eval_funcall function_entry2 ge m
    (Internal (compile_zrolled_program trillion_program)) [] E0 m (Vlong w).
Proof.
  intros w ge m DEN.
  eapply compile_zrolled_program_correct.
  - exact trillion_program_wf.
  - exact DEN.
Qed.

(* A compact, rolled Clight compiler for the scalar certificate DSL.

   Unlike [ClightDSLCompiler.compile_program], this compiler does not expand
   [dp_loop_count] copies of the loop body into the Clight AST.  It reserves
   one fresh temporary, emits one [Sloop], and proves the loop correct by
   induction on the source evaluator -- never by reducing a concrete loop
   count with [vm_compute].

   Boundary: [compile_rolled_program] is the canonical compact Clight AST
   proved in this file.  It is not claimed here to be syntactically equal to
   the AST currently produced by the C printer plus [clightgen] (that path
   uses an additional comparison scratch temporary and a different, but
   semantically equivalent, loop elaboration).  Connecting an emitted
   certificate to this theorem therefore requires either direct emission of
   this canonical AST or a separately checked AST correspondence theorem. *)

From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightFragmentSem Direct.ClightDefinedOps.
Require Import Direct.ClightDSLCompiler.

Import ListNotations.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------- *)
(* Source well-formedness and a structured (non-flattened) evaluator. *)

Definition doperand_wf (n: nat) (o: doperand) : Prop :=
  match o with
  | Dreg r => (r < n)%nat
  | Dlit _ | Didx => True
  end.

Definition dinstr_wf (n: nat) (i: dinstr) : Prop :=
  match i with
  | Dmov dst src => (dst < n)%nat /\ doperand_wf n src
  | Dbinop dst _ lhs rhs =>
      (dst < n)%nat /\ doperand_wf n lhs /\ doperand_wf n rhs
  end.

Record rolled_wf (p: dsl_program) : Prop := {
  rw_output: (dp_output p < dp_reg_count p)%nat;
  rw_init: Forall (dinstr_wf (dp_reg_count p)) (dp_init p);
  rw_body: Forall (dinstr_wf (dp_reg_count p)) (dp_body p);
  rw_epilogue: Forall (dinstr_wf (dp_reg_count p)) (dp_epilogue p);
  rw_loop_fits: Z.of_nat (dp_loop_count p) < Int64.modulus
}.

Lemma doperand_wf_succ:
  forall n o, doperand_wf n o -> doperand_wf (S n) o.
Proof. intros n o H; destruct o; cbn in *; lia. Qed.

Lemma dinstr_wf_succ:
  forall n i, dinstr_wf n i -> dinstr_wf (S n) i.
Proof.
  intros n i H; destruct i; cbn in H |- *.
  - destruct H as [D O]. split; [lia|now apply doperand_wf_succ].
  - destruct H as [D [L R]]. split; [lia|]. split;
      now apply doperand_wf_succ.
Qed.

Fixpoint eval_loop (idx count: nat) (body: list dinstr) (le: temp_env)
    : option temp_env :=
  match count with
  | O => Some le
  | S count' =>
      match eval_instrs idx body le with
      | Some le' => eval_loop (S idx) count' body le'
      | None => None
      end
  end.

Definition structured_denote (p: dsl_program) : option int64 :=
  match eval_instrs 0 (preamble (dp_reg_count p) ++ dp_init p)
      (initial_temps p) with
  | Some le1 =>
      match eval_loop 0 (dp_loop_count p) (dp_body p) le1 with
      | Some le2 =>
          match eval_instrs 0 (dp_epilogue p) le2 with
          | Some le3 =>
              match PTree.get (reg_ident (dp_output p)) le3 with
              | Some (Vlong w) => Some w
              | _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Lemma eval_trace_app:
  forall xs ys le,
  eval_trace (xs ++ ys) le =
    match eval_trace xs le with
    | Some le' => eval_trace ys le'
    | None => None
    end.
Proof.
  induction xs as [|[idx i] xs IH]; intros ys le; cbn; auto.
  destruct (eval_instr idx le i); auto.
Qed.

Lemma eval_trace_at_index:
  forall idx is le,
  eval_trace (at_index idx is) le = eval_instrs idx is le.
Proof.
  intros idx is; induction is as [|i is IH]; intros le; cbn; auto.
  destruct (eval_instr idx le i); auto.
Qed.

Lemma eval_instrs_app:
  forall idx xs ys le,
  eval_instrs idx (xs ++ ys) le =
    match eval_instrs idx xs le with
    | Some le' => eval_instrs idx ys le'
    | None => None
    end.
Proof.
  intros idx xs; induction xs as [|i xs IH]; intros ys le; cbn; auto.
  destruct (eval_instr idx le i); auto.
Qed.

Lemma eval_trace_loop_trace:
  forall idx count body le,
  eval_trace (loop_trace idx count body) le = eval_loop idx count body le.
Proof.
  intros idx count; revert idx.
  induction count as [|count IH]; intros idx body le.
  - reflexivity.
  - change
      (eval_trace
        (at_index idx body ++ loop_trace (S idx) count body) le =
       match eval_instrs idx body le with
       | Some le' => eval_loop (S idx) count body le'
       | None => None
       end).
    rewrite eval_trace_app, eval_trace_at_index.
    cbn [eval_loop].
    destruct (eval_instrs idx body le); auto.
Qed.

Lemma dsl_denote_structured:
  forall p, dsl_denote p = structured_denote p.
Proof.
  intros p.
  unfold dsl_denote, structured_denote, program_trace.
  rewrite eval_trace_app, eval_trace_at_index, eval_instrs_app.
  destruct (eval_instrs 0 (preamble (dp_reg_count p)) (initial_temps p));
    [|reflexivity].
  rewrite eval_trace_app, eval_trace_at_index.
  destruct (eval_instrs 0 (dp_init p) t); [|reflexivity].
  rewrite eval_trace_app, eval_trace_loop_trace.
  destruct (eval_loop 0 (dp_loop_count p) (dp_body p) t0);
    [|reflexivity].
  rewrite eval_trace_at_index.
  reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(* Compact Clight syntax. *)

Definition rolled_idx_ident (n: nat) : ident := reg_ident n.

Definition compile_rolled_operand (n: nat) (o: doperand) : expr :=
  match o with
  | Dreg r => Etempvar (reg_ident r) tulong
  | Dlit z => Econst_long (Int64.repr z) tulong
  | Didx => Etempvar (rolled_idx_ident n) tulong
  end.

Definition compile_rolled_rhs (n: nat) (op: dop)
    (lhs rhs: doperand) : expr :=
  Ecast
    (Ebinop (cop_of_dop op) (compile_rolled_operand n lhs)
      (compile_rolled_operand n rhs) (dop_result_type op))
    tulong.

Definition compile_rolled_instr (n: nat) (i: dinstr) : statement :=
  match i with
  | Dmov dst src =>
      Sset (reg_ident dst) (compile_rolled_operand n src)
  | Dbinop dst op lhs rhs =>
      Sset (reg_ident dst) (compile_rolled_rhs n op lhs rhs)
  end.

Fixpoint compile_rolled_instrs (n: nat) (is: list dinstr) : statement :=
  match is with
  | [] => Sskip
  | i :: rest =>
      Ssequence (compile_rolled_instr n i)
        (compile_rolled_instrs n rest)
  end.

Fixpoint compile_static_instrs (idx: nat) (is: list dinstr) : statement :=
  match is with
  | [] => Sskip
  | i :: rest =>
      Ssequence (compile_instr idx i) (compile_static_instrs idx rest)
  end.

Definition rolled_test (n limit: nat) : expr :=
  Ebinop Olt
    (Etempvar (rolled_idx_ident n) tulong)
    (Econst_long (Int64.repr (Z.of_nat limit)) tulong)
    tint.

Definition rolled_increment (n: nat) : statement :=
  Sset (rolled_idx_ident n)
    (Ebinop Oadd
      (Etempvar (rolled_idx_ident n) tulong)
      (Econst_long (Int64.repr 1) tulong)
      tulong).

Definition compile_rolled_loop (n limit: nat) (body: list dinstr)
    : statement :=
  Sloop
    (Sifthenelse (rolled_test n limit)
      (compile_rolled_instrs n body) Sbreak)
    (rolled_increment n).

Definition rolled_temp_decls (n: nat) : list (ident * type) :=
  (rolled_idx_ident n, tulong) :: temp_decls n.

Definition compile_rolled_body (p: dsl_program) : statement :=
  Ssequence
    (compile_static_instrs 0
      (preamble (dp_reg_count p) ++ dp_init p))
    (Ssequence
      (Sset (rolled_idx_ident (dp_reg_count p))
        (Econst_long Int64.zero tulong))
      (Ssequence
        (compile_rolled_loop (dp_reg_count p) (dp_loop_count p)
          (dp_body p))
        (Ssequence
          (compile_static_instrs 0 (dp_epilogue p))
          (Sreturn
            (Some (Etempvar (reg_ident (dp_output p)) tulong)))))).

Definition compile_rolled_program (p: dsl_program) : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := [];
  fn_vars := [];
  fn_temps := rolled_temp_decls (dp_reg_count p);
  fn_body := compile_rolled_body p
|}.

(* -------------------------------------------------------------------- *)
(* Register simulation.  The target contains the extra loop temporary, so
   equality of complete [PTree]s would be the wrong invariant. *)

Definition regs_agree (n: nat) (source target: temp_env) : Prop :=
  forall r, (r < n)%nat ->
    PTree.get (reg_ident r) source = PTree.get (reg_ident r) target.

Lemma reg_ident_inj:
  forall r s, reg_ident r = reg_ident s -> r = s.
Proof.
  intros r s H. exact (SuccNat2Pos.inj r s H).
Qed.

Lemma reg_ident_fresh:
  forall r n, (r < n)%nat -> reg_ident r <> rolled_idx_ident n.
Proof.
  intros r n LT EQ. apply reg_ident_inj in EQ. lia.
Qed.

Lemma initial_regs_agree:
  forall n,
  regs_agree n (create_undef_temps (temp_decls n))
    (create_undef_temps (rolled_temp_decls n)).
Proof.
  intros n r LT. unfold rolled_temp_decls; cbn.
  rewrite PTree.gso; auto using reg_ident_fresh.
Qed.

Lemma eval_operand_agree:
  forall n idx source target o,
  doperand_wf n o ->
  regs_agree n source target ->
  eval_operand idx source o = eval_operand idx target o.
Proof.
  intros n idx source target o WF AG.
  destruct o; cbn in WF |- *; auto.
  now rewrite (AG r WF).
Qed.

Lemma regs_agree_set:
  forall n source target dst w,
  (dst < n)%nat ->
  regs_agree n source target ->
  regs_agree n
    (PTree.set (reg_ident dst) (Vlong w) source)
    (PTree.set (reg_ident dst) (Vlong w) target).
Proof.
  intros n source target dst w DST AG r R.
  destruct (Nat.eq_dec r dst) as [->|NE].
  - now rewrite !PTree.gss.
  - rewrite !PTree.gso.
    + apply AG; exact R.
    + intro E; apply reg_ident_inj in E; auto.
    + intro E; apply reg_ident_inj in E; auto.
Qed.

Lemma eval_instr_sim:
  forall n idx i source target source',
  dinstr_wf n i ->
  regs_agree n source target ->
  eval_instr idx source i = Some source' ->
  exists target',
    eval_instr idx target i = Some target' /\
    regs_agree n source' target'.
Proof.
  intros n idx i source target source' WF AG RUN.
  destruct i as [dst src|dst op lhs rhs]; cbn in WF, RUN |- *.
  - destruct WF as [DST SWF].
    rewrite (eval_operand_agree n idx source target src SWF AG) in RUN.
    destruct (eval_operand idx target src) as [w|] eqn:E; try discriminate.
    inversion RUN; subst.
    eexists; split; [reflexivity|].
    now apply regs_agree_set.
  - destruct WF as [DST [LWF RWF]].
    rewrite (eval_operand_agree n idx source target lhs LWF AG) in RUN.
    rewrite (eval_operand_agree n idx source target rhs RWF AG) in RUN.
    destruct (eval_operand idx target lhs) as [a|] eqn:EL; try discriminate.
    destruct (eval_operand idx target rhs) as [b|] eqn:ER; try discriminate.
    destruct (eval_dop op a b) as [w|] eqn:EO; try discriminate.
    inversion RUN; subst.
    eexists; split; [reflexivity|].
    now apply regs_agree_set.
Qed.

Lemma eval_instrs_sim:
  forall n idx is source target source',
  Forall (dinstr_wf n) is ->
  regs_agree n source target ->
  eval_instrs idx is source = Some source' ->
  exists target',
    eval_instrs idx is target = Some target' /\
    regs_agree n source' target'.
Proof.
  intros n idx is; induction is as [|i is IH];
    intros source target source' WF AG RUN; cbn in RUN |- *.
  - inversion RUN; subst. eauto.
  - inversion WF as [|? ? IWF REST]; subst.
    destruct (eval_instr idx source i) as [source1|] eqn:STEP;
      try discriminate.
    destruct (eval_instr_sim n idx i source target source1 IWF AG STEP)
      as [target1 [TSTEP AG1]].
    rewrite TSTEP.
    now apply (IH source1 target1 source' REST AG1 RUN).
Qed.

Lemma eval_instr_preserves_idx:
  forall n idx i le le',
  dinstr_wf n i ->
  eval_instr idx le i = Some le' ->
  PTree.get (rolled_idx_ident n) le' =
    PTree.get (rolled_idx_ident n) le.
Proof.
  intros n idx i le le' WF RUN.
  destruct i as [dst src|dst op lhs rhs]; cbn in WF, RUN.
  - destruct WF as [DST _].
    destruct (eval_operand idx le src) as [w|]; try discriminate.
    inversion RUN; subst. rewrite PTree.gso; auto.
    now apply not_eq_sym, reg_ident_fresh.
  - destruct WF as [DST _].
    destruct (eval_operand idx le lhs) as [a|]; try discriminate.
    destruct (eval_operand idx le rhs) as [b|]; try discriminate.
    destruct (eval_dop op a b) as [w|]; try discriminate.
    inversion RUN; subst. rewrite PTree.gso; auto.
    now apply not_eq_sym, reg_ident_fresh.
Qed.

Lemma eval_instrs_preserves_idx:
  forall n idx is le le',
  Forall (dinstr_wf n) is ->
  eval_instrs idx is le = Some le' ->
  PTree.get (rolled_idx_ident n) le' =
    PTree.get (rolled_idx_ident n) le.
Proof.
  intros n idx is; induction is as [|i is IH];
    intros le le' WF RUN; cbn in RUN.
  - inversion RUN; reflexivity.
  - inversion WF as [|? ? IWF REST]; subst.
    destruct (eval_instr idx le i) as [le1|] eqn:STEP; try discriminate.
    rewrite (IH le1 le' REST RUN).
    now apply (eval_instr_preserves_idx n idx i le le1 IWF STEP).
Qed.

(* -------------------------------------------------------------------- *)
(* Correctness of straight-line and runtime-indexed instruction lists. *)

Lemma run_compile_static_instrs:
  forall ce m idx is le le',
  eval_instrs idx is le = Some le' ->
  run ce m (compile_static_instrs idx is) le =
    Some (le', Out_normal).
Proof.
  intros ce m idx is; induction is as [|i is IH];
    intros le le' RUN; cbn in RUN |- *.
  - inversion RUN; reflexivity.
  - destruct (eval_instr idx le i) as [le1|] eqn:STEP; try discriminate.
    rewrite (run_compile_instr ce m idx le i le1 STEP).
    exact (IH le1 le' RUN).
Qed.

Lemma eval_e_compile_rolled_operand:
  forall ce m n idx le o w,
  PTree.get (rolled_idx_ident n) le =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_operand idx le o = Some w ->
  eval_e ce m le (compile_rolled_operand n o) = Some (Vlong w).
Proof.
  intros ce m n idx le o w IDX EVAL.
  destruct o; cbn in EVAL |- *.
  - destruct (PTree.get (reg_ident r) le) as [v|] eqn:G;
      try discriminate.
    destruct v; try discriminate. inversion EVAL; subst; reflexivity.
  - inversion EVAL; reflexivity.
  - rewrite IDX. inversion EVAL; reflexivity.
Qed.

Lemma typeof_compile_rolled_operand:
  forall n o, typeof (compile_rolled_operand n o) = tulong.
Proof. intros n o; destruct o; reflexivity. Qed.

Lemma eval_e_compile_rolled_rhs:
  forall ce m n idx le op lhs rhs a b w,
  PTree.get (rolled_idx_ident n) le =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_operand idx le lhs = Some a ->
  eval_operand idx le rhs = Some b ->
  eval_dop op a b = Some w ->
  eval_e ce m le (compile_rolled_rhs n op lhs rhs) = Some (Vlong w).
Proof.
  intros ce m n idx le op lhs rhs a b w IDX HL HR HOP.
  unfold compile_rolled_rhs; cbn.
  rewrite (eval_e_compile_rolled_operand ce m n idx le lhs a IDX HL).
  rewrite (eval_e_compile_rolled_operand ce m n idx le rhs b IDX HR).
  rewrite !typeof_compile_rolled_operand.
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

Lemma run_compile_rolled_instr:
  forall ce m n idx le i le',
  PTree.get (rolled_idx_ident n) le =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_instr idx le i = Some le' ->
  run ce m (compile_rolled_instr n i) le = Some (le', Out_normal).
Proof.
  intros ce m n idx le i le' IDX RUN.
  destruct i as [dst src|dst op lhs rhs].
  - cbn [eval_instr] in RUN.
    destruct (eval_operand idx le src) as [w|] eqn:E; try discriminate.
    inversion RUN; subst.
    change
      (match eval_e ce m le (compile_rolled_operand n src) with
       | Some v => Some (PTree.set (reg_ident dst) v le, Out_normal)
       | None => None
       end = Some (PTree.set (reg_ident dst) (Vlong w) le, Out_normal)).
    now rewrite (eval_e_compile_rolled_operand ce m n idx le src w IDX E).
  - cbn [eval_instr] in RUN.
    destruct (eval_operand idx le lhs) as [a|] eqn:EL; try discriminate.
    destruct (eval_operand idx le rhs) as [b|] eqn:ER; try discriminate.
    destruct (eval_dop op a b) as [w|] eqn:EO; try discriminate.
    inversion RUN; subst.
    change
      (match eval_e ce m le (compile_rolled_rhs n op lhs rhs) with
       | Some v => Some (PTree.set (reg_ident dst) v le, Out_normal)
       | None => None
       end = Some (PTree.set (reg_ident dst) (Vlong w) le, Out_normal)).
    now rewrite
      (eval_e_compile_rolled_rhs ce m n idx le op lhs rhs a b w IDX EL ER EO).
Qed.

Lemma run_compile_rolled_instrs:
  forall ce m n idx is le le',
  Forall (dinstr_wf n) is ->
  PTree.get (rolled_idx_ident n) le =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_instrs idx is le = Some le' ->
  run ce m (compile_rolled_instrs n is) le = Some (le', Out_normal) /\
  PTree.get (rolled_idx_ident n) le' =
    Some (Vlong (Int64.repr (Z.of_nat idx))).
Proof.
  intros ce m n idx is; induction is as [|i is IH];
    intros le le' WF IDX RUN; cbn in RUN |- *.
  - inversion RUN; subst; auto.
  - inversion WF as [|? ? IWF REST]; subst.
    destruct (eval_instr idx le i) as [le1|] eqn:STEP; try discriminate.
    rewrite (run_compile_rolled_instr ce m n idx le i le1 IDX STEP).
    assert (IDX1 : PTree.get (rolled_idx_ident n) le1 =
        Some (Vlong (Int64.repr (Z.of_nat idx)))).
    { rewrite (eval_instr_preserves_idx n idx i le le1 IWF STEP). exact IDX. }
    exact (IH le1 le' REST IDX1 RUN).
Qed.

(* -------------------------------------------------------------------- *)
(* The actual rolled-loop simulation. *)

Lemma rolled_test_true:
  forall ge en m le n idx limit,
  PTree.get (rolled_idx_ident n) le =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  (idx < limit)%nat ->
  Z.of_nat limit < Int64.modulus ->
  eval_expr ge en le m (rolled_test n limit) (Vint Int.one) /\
  bool_val (Vint Int.one) tint m = Some true.
Proof.
  intros ge en m le n idx limit IDX LT FIT.
  assert (RANGEI : 0 <= Z.of_nat idx < Int64.modulus) by lia.
  assert (RANGEL : 0 <= Z.of_nat limit < Int64.modulus) by lia.
  split; [|reflexivity].
  unfold rolled_test.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr (Z.of_nat idx)))
    (v2 := Vlong (Int64.repr (Z.of_nat limit))).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop Int64.cmpu Int64.ltu Val.of_bool Vtrue Vfalse].
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
    destruct (zlt (Z.of_nat idx) (Z.of_nat limit)); [reflexivity|lia].
Qed.

Lemma rolled_test_false:
  forall ge en m le n limit,
  PTree.get (rolled_idx_ident n) le =
    Some (Vlong (Int64.repr (Z.of_nat limit))) ->
  Z.of_nat limit < Int64.modulus ->
  eval_expr ge en le m (rolled_test n limit) (Vint Int.zero) /\
  bool_val (Vint Int.zero) tint m = Some false.
Proof.
  intros ge en m le n limit IDX FIT.
  assert (RANGE : 0 <= Z.of_nat limit < Int64.modulus) by lia.
  split; [|reflexivity].
  unfold rolled_test.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr (Z.of_nat limit)))
    (v2 := Vlong (Int64.repr (Z.of_nat limit))).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop Int64.cmpu Int64.ltu Val.of_bool Vtrue Vfalse].
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
    destruct (zlt (Z.of_nat limit) (Z.of_nat limit)); [lia|reflexivity].
Qed.

Lemma rolled_increment_expr:
  forall ge en m le n idx,
  PTree.get (rolled_idx_ident n) le =
    Some (Vlong (Int64.repr (Z.of_nat idx))) ->
  eval_expr ge en le m
    (Ebinop Oadd
      (Etempvar (rolled_idx_ident n) tulong)
      (Econst_long (Int64.repr 1) tulong) tulong)
    (Vlong (Int64.repr (Z.of_nat (S idx)))).
Proof.
  intros ge en m le n idx IDX.
  eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr (Z.of_nat idx)))
    (v2 := Vlong (Int64.repr 1)).
  - apply eval_Etempvar. exact IDX.
  - apply eval_Econst_long.
  - rewrite sem_binary_operation_u64_exact.
    cbn [eval_u64_binop]. f_equal. f_equal.
    unfold Int64.add.
    apply Int64.eqm_samerepr.
    rewrite Nat2Z.inj_succ. apply Int64.eqm_add.
    + apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
    + apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
Qed.

Lemma regs_agree_set_idx:
  forall n source target w,
  regs_agree n source target ->
  regs_agree n source
    (PTree.set (rolled_idx_ident n) (Vlong w) target).
Proof.
  intros n source target w AG r LT.
  rewrite PTree.gso.
  - now apply AG.
  - now apply reg_ident_fresh.
Qed.

Theorem compile_rolled_loop_correct:
  forall fe ge en m n limit body start count source target source',
  Forall (dinstr_wf n) body ->
  Z.of_nat limit < Int64.modulus ->
  (start + count = limit)%nat ->
  regs_agree n source target ->
  PTree.get (rolled_idx_ident n) target =
    Some (Vlong (Int64.repr (Z.of_nat start))) ->
  eval_loop start count body source = Some source' ->
  exists target',
    ClightBigstep.exec_stmt fe ge en target m
      (compile_rolled_loop n limit body) E0 target' m Out_normal /\
    regs_agree n source' target' /\
    PTree.get (rolled_idx_ident n) target' =
      Some (Vlong (Int64.repr (Z.of_nat limit))).
Proof.
  intros fe ge en m n limit body start count.
  revert start.
  induction count as [|count IH];
    intros start source target source' WF FIT SUM AG IDX LOOP.
  - cbn in LOOP. inversion LOOP; subst source'.
    assert (EQ : start = limit) by lia. subst start.
    destruct (rolled_test_false ge en m target n limit IDX FIT)
      as [TEST BOOL].
    exists target. split.
    + unfold compile_rolled_loop.
      eapply exec_Sloop_stop1.
      * eapply exec_Sifthenelse with
          (v1 := Vint Int.zero) (b := false).
        -- exact TEST.
        -- exact BOOL.
        -- apply exec_Sbreak.
      * apply Out_break_or_return_B.
    + auto.
  - cbn in LOOP.
    destruct (eval_instrs start body source) as [source1|] eqn:BODY;
      try discriminate.
    destruct (eval_instrs_sim n start body source target source1 WF AG BODY)
      as [target1 [TBODY AG1]].
    destruct (run_compile_rolled_instrs (genv_cenv ge) m n start body
      target target1 WF IDX TBODY) as [RUNBODY IDX1].
    assert (LT : (start < limit)%nat) by lia.
    destruct (rolled_test_true ge en m target n start limit IDX LT FIT)
      as [TEST BOOL].
    set (target2 := PTree.set (rolled_idx_ident n)
      (Vlong (Int64.repr (Z.of_nat (S start)))) target1).
    assert (INCR : ClightBigstep.exec_stmt fe ge en target1 m
        (rolled_increment n) E0 target2 m Out_normal).
    { unfold rolled_increment, target2. apply exec_Sset.
      now apply rolled_increment_expr. }
    assert (AG2 : regs_agree n source1 target2).
    { unfold target2. now apply regs_agree_set_idx. }
    assert (IDX2 : PTree.get (rolled_idx_ident n) target2 =
        Some (Vlong (Int64.repr (Z.of_nat (S start))))).
    { unfold target2. now rewrite PTree.gss. }
    destruct (IH (S start) source1 target2 source' WF FIT ltac:(lia)
      AG2 IDX2 LOOP) as [target' [REST [AG' IDX']]].
    exists target'. split.
    + unfold compile_rolled_loop in REST |- *.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop.
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        -- exact TEST.
        -- exact BOOL.
        -- eapply run_sound. exact RUNBODY.
      * apply Out_normal_or_continue_N.
      * exact INCR.
      * exact REST.
    + auto.
Qed.

(* -------------------------------------------------------------------- *)
(* End-to-end function theorem. *)

Lemma preamble_wf:
  forall n, Forall (dinstr_wf n) (preamble n).
Proof.
  induction n as [|n IH].
  - constructor.
  - cbn. rewrite Forall_app. split.
    + eapply Forall_impl; [|exact IH]. intros i H.
      now apply dinstr_wf_succ.
    + constructor; [cbn; lia|constructor].
Qed.

Lemma compile_rolled_body_correct:
  forall p w fe ge en m,
  rolled_wf p ->
  dsl_denote p = Some w ->
  exists le',
    ClightBigstep.exec_stmt fe ge en
      (create_undef_temps (fn_temps (compile_rolled_program p))) m
      (fn_body (compile_rolled_program p)) E0 le' m
      (Out_return (Some (Vlong w, tulong))).
Proof.
  intros p w fe ge en m WF DEN.
  destruct WF as [OUT INIT BODY EPI FIT].
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
    (fn_temps (compile_rolled_program p))).
  assert (AG0 : regs_agree (dp_reg_count p) (initial_temps p) target0).
  { unfold target0, compile_rolled_program, initial_temps; cbn.
    apply initial_regs_agree. }
  assert (PREFIX_WF : Forall (dinstr_wf (dp_reg_count p))
      (preamble (dp_reg_count p) ++ dp_init p)).
  { rewrite Forall_app. auto using preamble_wf. }
  destruct (eval_instrs_sim (dp_reg_count p) 0
      (preamble (dp_reg_count p) ++ dp_init p)
      (initial_temps p) target0 source1 PREFIX_WF AG0 PREFIX)
    as [target1 [TPREFIX AG1]].
  assert (XPREFIX : ClightBigstep.exec_stmt fe ge en target0 m
      (compile_static_instrs 0
        (preamble (dp_reg_count p) ++ dp_init p))
      E0 target1 m Out_normal).
  { apply run_sound.
    now apply run_compile_static_instrs. }

  set (target1i := PTree.set (rolled_idx_ident (dp_reg_count p))
    (Vlong Int64.zero) target1).
  assert (XINIT : ClightBigstep.exec_stmt fe ge en target1 m
      (Sset (rolled_idx_ident (dp_reg_count p))
        (Econst_long Int64.zero tulong)) E0 target1i m Out_normal).
  { unfold target1i. apply exec_Sset. constructor. }
  assert (AG1I : regs_agree (dp_reg_count p) source1 target1i).
  { unfold target1i. now apply regs_agree_set_idx. }
  assert (IDX0 : PTree.get (rolled_idx_ident (dp_reg_count p)) target1i =
      Some (Vlong (Int64.repr (Z.of_nat 0)))).
  { unfold target1i. rewrite PTree.gss. reflexivity. }
  destruct (compile_rolled_loop_correct fe ge en m
      (dp_reg_count p) (dp_loop_count p) (dp_body p)
      0 (dp_loop_count p) source1 target1i source2
      BODY FIT ltac:(lia) AG1I IDX0 LOOP)
    as [target2 [XLOOP [AG2 IDX2]]].

  destruct (eval_instrs_sim (dp_reg_count p) 0 (dp_epilogue p)
      source2 target2 source3 EPI AG2 EPILOGUE)
    as [target3 [TEPI AG3]].
  assert (XEPI : ClightBigstep.exec_stmt fe ge en target2 m
      (compile_static_instrs 0 (dp_epilogue p))
      E0 target3 m Out_normal).
  { apply run_sound. now apply run_compile_static_instrs. }
  assert (TOUTPUT : PTree.get (reg_ident (dp_output p)) target3 =
      Some (Vlong w)).
  { rewrite <- (AG3 (dp_output p) OUT). exact OUTPUT. }
  assert (XRETURN : ClightBigstep.exec_stmt fe ge en target3 m
      (Sreturn (Some (Etempvar (reg_ident (dp_output p)) tulong)))
      E0 target3 m (Out_return (Some (Vlong w, tulong)))).
  { apply exec_Sreturn_some. now apply eval_Etempvar. }

  exists target3.
  unfold compile_rolled_program, compile_rolled_body; cbn.
  change E0 with (E0 ** (E0 ** (E0 ** (E0 ** E0)))).
  eapply exec_Sseq_1; [exact XPREFIX|].
  eapply exec_Sseq_1; [exact XINIT|].
  eapply exec_Sseq_1; [exact XLOOP|].
  eapply exec_Sseq_1; [exact XEPI|exact XRETURN].
Qed.

Theorem compile_rolled_program_correct:
  forall p w ge m,
  rolled_wf p ->
  dsl_denote p = Some w ->
  ClightBigstep.eval_funcall function_entry2 ge m
    (Internal (compile_rolled_program p)) [] E0 m (Vlong w).
Proof.
  intros p w ge m WF DEN.
  destruct (compile_rolled_body_correct p w function_entry2 ge empty_env m
    WF DEN) as [le' BODY].
  eapply eval_funcall_internal with
    (e := empty_env) (le1 := create_undef_temps
      (fn_temps (compile_rolled_program p)))
    (le2 := le') (m1 := m) (m2 := m) (out :=
      Out_return (Some (Vlong w, tulong))).
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

(* The syntactic size of the loop is independent of [dp_loop_count]: there is
   exactly one [Sloop] and one copy of [dp_body].  The end-to-end theorem above
   is correspondingly symbolic in [p], [w], [ge], and [m]. *)

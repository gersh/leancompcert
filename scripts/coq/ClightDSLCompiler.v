(* A proved compiler from the lean-compcert scalar certificate DSL to the
   exact CompCert Clight AST.  Generated certificate files contain only a
   [dsl_program] value and define their function with [compile_program]. *)

From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightFragmentSem Direct.ClightDefinedOps.

Import ListNotations.
Local Open Scope Z_scope.

Inductive doperand : Type :=
  | Dreg (r: nat)
  | Dlit (z: Z)
  | Didx.

Inductive dop : Type :=
  | Dadd | Dsub | Dmul | Ddiv | Dmod
  | Dand | Dor | Dxor | Dshl | Dshr
  | Deq | Dne | Dlt | Dle | Dgt | Dge.

Inductive dinstr : Type :=
  | Dmov (dst: nat) (src: doperand)
  | Dbinop (dst: nat) (op: dop) (lhs rhs: doperand).

Record dsl_program : Type := {
  dp_reg_count: nat;
  dp_loop_count: nat;
  dp_init: list dinstr;
  dp_body: list dinstr;
  dp_epilogue: list dinstr;
  dp_output: nat
}.

Definition reg_ident (r: nat) : ident := Pos.of_succ_nat r.

Definition cop_of_dop (op: dop) : binary_operation :=
  match op with
  | Dadd => Oadd | Dsub => Osub | Dmul => Omul
  | Ddiv => Odiv | Dmod => Omod
  | Dand => Oand | Dor => Oor | Dxor => Oxor
  | Dshl => Oshl | Dshr => Oshr
  | Deq => Oeq | Dne => One | Dlt => Olt
  | Dle => Ole | Dgt => Ogt | Dge => Oge
  end.

Definition dop_result_type (op: dop) : type :=
  match op with
  | Deq | Dne | Dlt | Dle | Dgt | Dge => tint
  | _ => tulong
  end.

Definition eval_operand (idx: nat) (le: temp_env) (o: doperand)
    : option int64 :=
  match o with
  | Dreg r =>
      match PTree.get (reg_ident r) le with
      | Some (Vlong w) => Some w
      | _ => None
      end
  | Dlit z => Some (Int64.repr z)
  | Didx => Some (Int64.repr (Z.of_nat idx))
  end.

(** Convert the numerical result of a CompCert binary operation to the u64
    register value used by the DSL. Comparisons return a [Vint] before their
    generated cast; arithmetic returns a [Vlong]. *)
Definition val_u64 (v: val) : option int64 :=
  match v with
  | Vlong w => Some w
  | Vint i => Some (Int64.repr (Int.unsigned i))
  | _ => None
  end.

Definition eval_dop (op: dop) (a b: int64) : option int64 :=
  match eval_u64_binop (cop_of_dop op) a b with
  | Some v => val_u64 v
  | None => None
  end.

Definition eval_instr (idx: nat) (le: temp_env) (i: dinstr)
    : option temp_env :=
  match i with
  | Dmov dst src =>
      match eval_operand idx le src with
      | Some w => Some (PTree.set (reg_ident dst) (Vlong w) le)
      | None => None
      end
  | Dbinop dst op lhs rhs =>
      match eval_operand idx le lhs, eval_operand idx le rhs with
      | Some a, Some b =>
          match eval_dop op a b with
          | Some w => Some (PTree.set (reg_ident dst) (Vlong w) le)
          | None => None
          end
      | _, _ => None
      end
  end.

Fixpoint eval_instrs (idx: nat) (is: list dinstr) (le: temp_env)
    : option temp_env :=
  match is with
  | [] => Some le
  | i :: rest =>
      match eval_instr idx le i with
      | Some le' => eval_instrs idx rest le'
      | None => None
      end
  end.

Fixpoint preamble (n: nat) : list dinstr :=
  match n with
  | O => []
  | S n' => preamble n' ++ [Dmov n' (Dlit 0)]
  end.

Fixpoint loop_trace (idx count: nat) (body: list dinstr)
    : list (nat * dinstr) :=
  match count with
  | O => []
  | S count' =>
      map (fun i => (idx, i)) body ++ loop_trace (S idx) count' body
  end.

Definition at_index (idx: nat) (is: list dinstr) : list (nat * dinstr) :=
  map (fun i => (idx, i)) is.

Definition program_trace (p: dsl_program) : list (nat * dinstr) :=
  at_index 0 (preamble (dp_reg_count p)) ++
  at_index 0 (dp_init p) ++
  loop_trace 0 (dp_loop_count p) (dp_body p) ++
  at_index 0 (dp_epilogue p).

Fixpoint eval_trace (trace: list (nat * dinstr)) (le: temp_env)
    : option temp_env :=
  match trace with
  | [] => Some le
  | (idx, i) :: rest =>
      match eval_instr idx le i with
      | Some le' => eval_trace rest le'
      | None => None
      end
  end.

Definition temp_decls (n: nat) : list (ident * type) :=
  map (fun r => (reg_ident r, tulong)) (seq 0 n).

Definition initial_temps (p: dsl_program) : temp_env :=
  create_undef_temps (temp_decls (dp_reg_count p)).

Definition dsl_denote (p: dsl_program) : option int64 :=
  match eval_trace (program_trace p) (initial_temps p) with
  | Some le =>
      match PTree.get (reg_ident (dp_output p)) le with
      | Some (Vlong w) => Some w
      | _ => None
      end
  | None => None
  end.

Definition compile_operand (idx: nat) (o: doperand) : expr :=
  match o with
  | Dreg r => Etempvar (reg_ident r) tulong
  | Dlit z => Econst_long (Int64.repr z) tulong
  | Didx => Econst_long (Int64.repr (Z.of_nat idx)) tulong
  end.

Definition compile_rhs (idx: nat) (op: dop)
    (lhs rhs: doperand) : expr :=
  Ecast
    (Ebinop (cop_of_dop op) (compile_operand idx lhs)
      (compile_operand idx rhs) (dop_result_type op))
    tulong.

Definition compile_instr (idx: nat) (i: dinstr) : statement :=
  match i with
  | Dmov dst src => Sset (reg_ident dst) (compile_operand idx src)
  | Dbinop dst op lhs rhs =>
      Sset (reg_ident dst) (compile_rhs idx op lhs rhs)
  end.

Fixpoint compile_trace (trace: list (nat * dinstr)) (tail: statement)
    : statement :=
  match trace with
  | [] => tail
  | (idx, i) :: rest =>
      Ssequence (compile_instr idx i) (compile_trace rest tail)
  end.

Definition compile_body (p: dsl_program) : statement :=
  compile_trace (program_trace p)
    (Sreturn (Some (Etempvar (reg_ident (dp_output p)) tulong))).

Definition compile_program (p: dsl_program) : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := [];
  fn_vars := [];
  fn_temps := temp_decls (dp_reg_count p);
  fn_body := compile_body p
|}.

Definition empty_ge : genv := {|
  genv_genv := @Genv.empty_genv fundef type [];
  genv_cenv := PTree.empty composite
|}.

Lemma typeof_compile_operand:
  forall idx o, typeof (compile_operand idx o) = tulong.
Proof. intros idx o; destruct o; reflexivity. Qed.

Lemma eval_e_compile_operand:
  forall ce m idx le o w,
  eval_operand idx le o = Some w ->
  eval_e ce m le (compile_operand idx o) = Some (Vlong w).
Proof.
  intros ce m idx le o w H; destruct o; cbn in H |- *.
  - destruct (PTree.get (reg_ident r) le) as [v|] eqn:G; try discriminate.
    destruct v; try discriminate. inversion H; subst; reflexivity.
  - inversion H; reflexivity.
  - inversion H; reflexivity.
Qed.

Lemma eval_e_compile_rhs:
  forall ce m idx le op lhs rhs a b w,
  eval_operand idx le lhs = Some a ->
  eval_operand idx le rhs = Some b ->
  eval_dop op a b = Some w ->
  eval_e ce m le (compile_rhs idx op lhs rhs) = Some (Vlong w).
Proof.
  intros ce m idx le op lhs rhs a b w HL HR HOP.
  unfold compile_rhs; cbn.
  rewrite (eval_e_compile_operand ce m idx le lhs a HL).
  rewrite (eval_e_compile_operand ce m idx le rhs b HR).
  rewrite !typeof_compile_operand.
  assert (BOK : binop_ok (cop_of_dop op) tulong tulong = true)
    by (destruct op; reflexivity).
  rewrite BOK.
  rewrite sem_binary_operation_u64_exact.
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

Lemma run_compile_instr:
  forall ce m idx le i le',
  eval_instr idx le i = Some le' ->
  run ce m (compile_instr idx i) le = Some (le', Out_normal).
Proof.
  intros ce m idx le i le' H; destruct i.
  - cbn [eval_instr] in H.
    destruct (eval_operand idx le src) as [w|] eqn:E; try discriminate.
    inversion H; subst.
    change
      (match eval_e ce m le (compile_operand idx src) with
       | Some v => Some (PTree.set (reg_ident dst) v le, Out_normal)
       | None => None
       end = Some (PTree.set (reg_ident dst) (Vlong w) le, Out_normal)).
    now rewrite (eval_e_compile_operand ce m idx le src w E).
  - cbn [eval_instr] in H.
    destruct (eval_operand idx le lhs) as [a|] eqn:EL; try discriminate.
    destruct (eval_operand idx le rhs) as [b|] eqn:ER; try discriminate.
    destruct (eval_dop op a b) as [w|] eqn:EO; try discriminate.
    inversion H; subst.
    change
      (match eval_e ce m le (compile_rhs idx op lhs rhs) with
       | Some v => Some (PTree.set (reg_ident dst) v le, Out_normal)
       | None => None
       end = Some (PTree.set (reg_ident dst) (Vlong w) le, Out_normal)).
    now rewrite (eval_e_compile_rhs ce m idx le op lhs rhs a b w EL ER EO).
Qed.

Lemma run_compile_trace:
  forall ce m trace le le' tail,
  eval_trace trace le = Some le' ->
  run ce m (compile_trace trace tail) le = run ce m tail le'.
Proof.
  intros ce m trace; induction trace as [|[idx i] rest IH];
    intros le le' tail H; cbn in H |- *.
  - inversion H; reflexivity.
  - destruct (eval_instr idx le i) as [mid|] eqn:E; try discriminate.
    rewrite (run_compile_instr ce m idx le i mid E).
    exact (IH mid le' tail H).
Qed.

Theorem compile_program_run:
  forall p w,
  dsl_denote p = Some w ->
  exists le',
    run (genv_cenv empty_ge) Mem.empty
      (fn_body (compile_program p))
      (create_undef_temps (fn_temps (compile_program p))) =
    Some (le', Out_return (Some (Vlong w, tulong))).
Proof.
  intros p w H.
  unfold dsl_denote in H.
  destruct (eval_trace (program_trace p) (initial_temps p))
    as [le'|] eqn:E; try discriminate.
  destruct (PTree.get (reg_ident (dp_output p)) le')
    as [v|] eqn:G; try discriminate.
  destruct v; try discriminate. inversion H; subst.
  exists le'.
  unfold initial_temps in E.
  unfold compile_program, compile_body, initial_temps; cbn.
  rewrite (run_compile_trace (PTree.empty composite) Mem.empty
    (program_trace p) (create_undef_temps (temp_decls (dp_reg_count p)))
    le' (Sreturn (Some (Etempvar (reg_ident (dp_output p)) tulong))) E).
  cbn. rewrite G. reflexivity.
Qed.

(** Generic end-to-end theorem for the exact AST returned by
    [compile_program]. *)
Theorem compile_program_correct:
  forall p w ge m,
  dsl_denote p = Some w ->
  ClightBigstep.eval_funcall function_entry2 ge m
    (Internal (compile_program p)) [] E0 m (Vlong w).
Proof.
  intros p w ge m DEN.
  destruct (compile_program_run p w DEN) as [le' RUN].
  eapply run_funcall2 with (le' := le') (v := Vlong w) (ty := tulong).
  - reflexivity.
  - reflexivity.
  - discriminate.
  - rewrite (run_indep (fn_body (compile_program p))
      (genv_cenv ge) (PTree.empty composite) m Mem.empty
      (create_undef_temps (fn_temps (compile_program p)))).
    exact RUN.
  - reflexivity.
Qed.

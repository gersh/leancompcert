(* Exact Clight compiler for the C text emitted by Reflect.emitRolled.

   This differs deliberately from ClightRolledCompiler's compact canonical
   AST: it models clightgen's normalization of the actual emitted C, including
   the u8 comparison scratch, declaration-initializer hoisting, Swhile shape,
   and the absence of administrative trailing Sskip nodes. *)

From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightFragmentSem Direct.ClightDefinedOps.
Require Import Direct.ClightDSLCompiler Direct.ClightRolledCompiler.

Import ListNotations.
Local Open Scope Z_scope.

Record emitter_layout : Type := {
  el_scratch : ident;
  el_regs : list ident;
  el_counter : ident
}.

Definition el_reg (l: emitter_layout) (r: nat) : ident :=
  nth r (el_regs l) 1%positive.

Record emitter_layout_wf (l: emitter_layout) (n: nat) : Prop := {
  el_regs_length : length (el_regs l) = n;
  el_regs_nodup : NoDup (el_regs l);
  el_scratch_fresh : ~ In (el_scratch l) (el_regs l);
  el_counter_fresh : ~ In (el_counter l) (el_regs l);
  el_scratch_counter : el_scratch l <> el_counter l
}.

(** Count-free syntax payload.  Keeping the semantic [dp_loop_count] out of
    this record is essential: an exact-AST conversion must not normalize a
    closed [Z.to_nat] at a trillion-scale loop bound merely to discover that
    syntax generation never inspects it. *)
Record emitter_source : Type := {
  es_reg_count : nat;
  es_init : list dinstr;
  es_body : list dinstr;
  es_epilogue : list dinstr;
  es_output : nat
}.

Definition emitter_source_of_program (p: dsl_program) : emitter_source := {|
  es_reg_count := dp_reg_count p;
  es_init := dp_init p;
  es_body := dp_body p;
  es_epilogue := dp_epilogue p;
  es_output := dp_output p
|}.

Record emitter_source_matches (s: emitter_source) (p: dsl_program) : Prop := {
  esm_reg_count : es_reg_count s = dp_reg_count p;
  esm_init : es_init s = dp_init p;
  esm_body : es_body s = dp_body p;
  esm_epilogue : es_epilogue s = dp_epilogue p;
  esm_output : es_output s = dp_output p
}.

Lemma emitter_source_of_program_matches:
  forall p, emitter_source_matches (emitter_source_of_program p) p.
Proof. intros p; constructor; reflexivity. Qed.

Definition emitter_temp_decls (l: emitter_layout) : list (ident * type) :=
  (el_scratch l, tuchar) ::
  map (fun x => (x, tulong)) (el_regs l) ++ [(el_counter l, tulong)].

Definition emitter_operand (l: emitter_layout) (idx: expr)
    (o: doperand) : expr :=
  match o with
  | Dreg r => Etempvar (el_reg l r) tulong
  | Dlit z => Econst_long (Int64.repr z) tulong
  | Didx => idx
  end.

Definition emitter_static_operand (l: emitter_layout) (idx: nat)
    (o: doperand) : expr :=
  emitter_operand l (Econst_long (Int64.repr (Z.of_nat idx)) tulong) o.

Definition emitter_dynamic_operand (l: emitter_layout) (o: doperand) : expr :=
  emitter_operand l (Etempvar (el_counter l) tulong) o.

Definition dop_is_comparison (op: dop) : bool :=
  match op with
  | Deq | Dne | Dlt | Dle | Dgt | Dge => true
  | _ => false
  end.

Definition emitter_instr (l: emitter_layout) (idx: expr)
    (i: dinstr) : list statement :=
  match i with
  | Dmov dst src => [Sset (el_reg l dst) (emitter_operand l idx src)]
  | Dbinop dst op lhs rhs =>
      let e := Ebinop (cop_of_dop op)
        (emitter_operand l idx lhs) (emitter_operand l idx rhs)
        (dop_result_type op) in
      if dop_is_comparison op then
        [Sset (el_scratch l) (Ecast e tuchar);
         Sset (el_reg l dst)
           (Ecast (Etempvar (el_scratch l) tuchar) tulong)]
      else
        [Sset (el_reg l dst) e]
  end.

Fixpoint emitter_instrs (l: emitter_layout) (idx: expr)
    (is: list dinstr) : list statement :=
  match is with
  | [] => []
  | i :: rest => emitter_instr l idx i ++ emitter_instrs l idx rest
  end.

Fixpoint emitter_sequence (ss: list statement) : statement :=
  match ss with
  | [] => Sskip
  | [s] => s
  | s :: rest => Ssequence s (emitter_sequence rest)
  end.

Definition emitter_test (l: emitter_layout) (limit: Z) : expr :=
  Ebinop Olt (Etempvar (el_counter l) tulong)
    (Econst_long (Int64.repr limit) tulong) tint.

Definition emitter_increment (l: emitter_layout) : statement :=
  Sset (el_counter l)
    (Ebinop Oadd (Etempvar (el_counter l) tulong)
      (Econst_long (Int64.repr 1) tulong) tulong).

Definition emitter_loop_body (l: emitter_layout) (body: list dinstr)
    : statement :=
  emitter_sequence
    (emitter_instrs l (Etempvar (el_counter l) tulong) body ++
      [emitter_increment l]).

Definition emitter_loop (l: emitter_layout) (limit: Z)
    (body: list dinstr) : statement :=
  Swhile (emitter_test l limit) (emitter_loop_body l body).

Definition emitter_counter_zero (l: emitter_layout) : statement :=
  Sset (el_counter l) (Econst_long Int64.zero tulong).

Definition emitter_scratch_zero (l: emitter_layout) : statement :=
  Sset (el_scratch l) (Ecast (Econst_int Int.zero tint) tuchar).

Definition emitter_body_statements (l: emitter_layout) (loop_limit: Z)
    (s: emitter_source)
    : list statement :=
  [emitter_counter_zero l; emitter_scratch_zero l] ++
  emitter_instrs l (Econst_long Int64.zero tulong)
    (preamble (es_reg_count s) ++ es_init s) ++
  [emitter_loop l loop_limit (es_body s)] ++
  emitter_instrs l (Econst_long Int64.zero tulong) (es_epilogue s) ++
  [Sreturn (Some (Etempvar (el_reg l (es_output s)) tulong))].

Definition compile_emitted_rolled_body (l: emitter_layout) (loop_limit: Z)
    (s: emitter_source) : statement :=
  emitter_sequence (emitter_body_statements l loop_limit s).

Definition compile_emitted_rolled_program
    (l: emitter_layout) (loop_limit: Z) (s: emitter_source) : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := [];
  fn_vars := [];
  fn_temps := emitter_temp_decls l;
  fn_body := compile_emitted_rolled_body l loop_limit s
|}.

(* The exact compiler is compact: [dp_loop_count] occurs only in the loop
   guard literal and never controls syntax generation. *)

(* -------------------------------------------------------------------- *)
(* Layout facts and register simulation. *)

Definition emitter_regs_agree (l: emitter_layout) (n: nat)
    (source target: temp_env) : Prop :=
  forall r, (r < n)%nat ->
    PTree.get (reg_ident r) source = PTree.get (el_reg l r) target.

Lemma el_reg_in:
  forall l n r,
  emitter_layout_wf l n ->
  (r < n)%nat ->
  In (el_reg l r) (el_regs l).
Proof.
  intros l n r WF LT.
  destruct WF as [LEN ND SF CF SC].
  unfold el_reg. apply nth_In. lia.
Qed.

Lemma el_reg_inj:
  forall l n r s,
  emitter_layout_wf l n ->
  (r < n)%nat -> (s < n)%nat ->
  el_reg l r = el_reg l s -> r = s.
Proof.
  intros l n r s WF R S EQ.
  destruct WF as [LEN ND SF CF SC].
  unfold el_reg in EQ.
  apply (proj1 (NoDup_nth (el_regs l) 1%positive) ND r s); auto; lia.
Qed.

Lemma el_reg_ne_scratch:
  forall l n r,
  emitter_layout_wf l n -> (r < n)%nat ->
  el_reg l r <> el_scratch l.
Proof.
  intros l n r WF LT EQ.
  destruct WF as [LEN ND SF CF SC].
  apply SF. rewrite <- EQ. unfold el_reg. apply nth_In. lia.
Qed.

Lemma el_reg_ne_counter:
  forall l n r,
  emitter_layout_wf l n -> (r < n)%nat ->
  el_reg l r <> el_counter l.
Proof.
  intros l n r WF LT EQ.
  destruct WF as [LEN ND SF CF SC].
  apply CF. rewrite <- EQ. unfold el_reg. apply nth_In. lia.
Qed.

Lemma create_undef_temps_present:
  forall vars x ty,
  In (x, ty) vars ->
  PTree.get x (create_undef_temps vars) = Some Vundef.
Proof.
  induction vars as [|[y u] vars IH]; intros x ty IN; cbn in *.
  - contradiction.
  - destruct IN as [EQ|IN].
    + inversion EQ; subst. apply PTree.gss.
    + rewrite PTree.gsspec. destruct (peq x y) as [EQ|NE].
      * reflexivity.
      * now apply IH with (ty := ty).
Qed.

Lemma temp_decl_in:
  forall n r,
  (r < n)%nat ->
  In (reg_ident r, tulong) (temp_decls n).
Proof.
  intros n r LT. unfold temp_decls.
  apply in_map_iff. exists r. split; [reflexivity|].
  apply in_seq. lia.
Qed.

Lemma emitter_temp_decl_in:
  forall l n r,
  emitter_layout_wf l n ->
  (r < n)%nat ->
  In (el_reg l r, tulong) (emitter_temp_decls l).
Proof.
  intros l n r WF LT. unfold emitter_temp_decls.
  right. apply in_or_app. left. apply in_map_iff.
  exists (el_reg l r). split; [reflexivity|].
  now apply el_reg_in with (n := n).
Qed.

Lemma initial_emitter_regs_agree:
  forall l n,
  emitter_layout_wf l n ->
  emitter_regs_agree l n
    (create_undef_temps (temp_decls n))
    (create_undef_temps (emitter_temp_decls l)).
Proof.
  intros l n WF r LT.
  rewrite (create_undef_temps_present _ _ _ (temp_decl_in n r LT)).
  rewrite (create_undef_temps_present _ _ _
    (emitter_temp_decl_in l n r WF LT)).
  reflexivity.
Qed.

Lemma emitter_regs_agree_set:
  forall l n source target dst w,
  emitter_layout_wf l n ->
  (dst < n)%nat ->
  emitter_regs_agree l n source target ->
  emitter_regs_agree l n
    (PTree.set (reg_ident dst) (Vlong w) source)
    (PTree.set (el_reg l dst) (Vlong w) target).
Proof.
  intros l n source target dst w WF DST AG r R.
  destruct (Nat.eq_dec r dst) as [->|NE].
  - now rewrite !PTree.gss.
  - rewrite !PTree.gso.
    + apply AG; exact R.
    + intro E. apply (el_reg_inj l n r dst WF R DST) in E. auto.
    + intro E. apply reg_ident_inj in E. auto.
Qed.

Lemma emitter_regs_agree_set_scratch:
  forall l n source target v,
  emitter_layout_wf l n ->
  emitter_regs_agree l n source target ->
  emitter_regs_agree l n source
    (PTree.set (el_scratch l) v target).
Proof.
  intros l n source target v WF AG r R.
  rewrite PTree.gso.
  - apply AG; exact R.
  - now apply el_reg_ne_scratch with (n := n).
Qed.

Lemma emitter_regs_agree_set_counter:
  forall l n source target v,
  emitter_layout_wf l n ->
  emitter_regs_agree l n source target ->
  emitter_regs_agree l n source
    (PTree.set (el_counter l) v target).
Proof.
  intros l n source target v WF AG r R.
  rewrite PTree.gso.
  - apply AG; exact R.
  - now apply el_reg_ne_counter with (n := n).
Qed.

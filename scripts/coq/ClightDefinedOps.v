(* Dynamic definedness contract for the u64 fragment emitted by lean-compcert.

   This file deliberately states the guards using CompCert's own operations.
   In particular, shifts are guarded by [Int64.ltu b Int64.iwordsize], which
   is exactly the condition used by [Cop.sem_shift], and unsigned division
   and remainder exclude [Int64.zero]. *)

From compcert Require Import Coqlib Integers Values Memory.
From compcert Require Import AST Ctypes Cop Clight Clightdefs.

(** The Coq counterpart of Lean's [ClightContract.instrDefined]. *)
Definition u64_op_defined (op: binary_operation) (b: int64) : bool :=
  match op with
  | Odiv | Omod => negb (Int64.eq b Int64.zero)
  | Oshl | Oshr => Int64.ltu b Int64.iwordsize
  | _ => true
  end.

(** Arithmetic form of the same guard. This is the form mirrored by the
    Lean predicate after every operand has been reduced to [0, 2^64). *)
Definition source_u64_op_defined (op: binary_operation) (b: Z) : Prop :=
  match op with
  | Odiv | Omod => b <> 0
  | Oshl | Oshr => b < 64
  | _ => True
  end.

(** Exact value-level semantics of the source DSL's u64 operations, expressed
    using CompCert integers.  Partial operations return [None] at exactly the
    guard failures above. *)
Definition eval_u64_binop (op: binary_operation) (a b: int64) : option val :=
  match op with
  | Oadd => Some (Vlong (Int64.add a b))
  | Osub => Some (Vlong (Int64.sub a b))
  | Omul => Some (Vlong (Int64.mul a b))
  | Odiv =>
      if Int64.eq b Int64.zero then None
      else Some (Vlong (Int64.divu a b))
  | Omod =>
      if Int64.eq b Int64.zero then None
      else Some (Vlong (Int64.modu a b))
  | Oand => Some (Vlong (Int64.and a b))
  | Oor => Some (Vlong (Int64.or a b))
  | Oxor => Some (Vlong (Int64.xor a b))
  | Oshl =>
      if Int64.ltu b Int64.iwordsize
      then Some (Vlong (Int64.shl a b)) else None
  | Oshr =>
      if Int64.ltu b Int64.iwordsize
      then Some (Vlong (Int64.shru a b)) else None
  | Oeq => Some (Val.of_bool (Int64.cmpu Ceq a b))
  | One => Some (Val.of_bool (Int64.cmpu Cne a b))
  | Olt => Some (Val.of_bool (Int64.cmpu Clt a b))
  | Ogt => Some (Val.of_bool (Int64.cmpu Cgt a b))
  | Ole => Some (Val.of_bool (Int64.cmpu Cle a b))
  | Oge => Some (Val.of_bool (Int64.cmpu Cge a b))
  end.

(** CompCert understands each emitted u64 binary expression exactly as the
    source operation above.  No custom C semantics occurs in this statement. *)
Theorem sem_binary_operation_u64_exact:
  forall ce m op a b,
  sem_binary_operation ce op (Vlong a) tulong (Vlong b) tulong m =
  eval_u64_binop op a b.
Proof.
  intros ce m op a b.
  destruct Archi.ptr64 eqn:PTR; destruct op;
    cbv [tulong eval_u64_binop sem_binary_operation
      sem_add sem_sub sem_mul sem_div sem_mod
      sem_and sem_or sem_xor sem_shl sem_shr sem_cmp
      sem_shift sem_binarith sem_cast classify_cast
      classify_binarith binarith_type classify_add classify_sub
      classify_shift classify_cmp typeconv] in *;
    try rewrite PTR in *; reflexivity.
Qed.

Theorem u64_op_defined_repr:
  forall op b,
  0 <= b < Int64.modulus ->
  (u64_op_defined op (Int64.repr b) = true <->
   source_u64_op_defined op b).
Proof.
  intros op b RANGE; destruct op; cbn [u64_op_defined source_u64_op_defined];
    try tauto.
  - unfold Int64.eq. rewrite Int64.unsigned_repr_eq. rewrite Z.mod_small by exact RANGE.
    rewrite Int64.unsigned_zero. destruct (zeq b 0); cbn; lia.
  - unfold Int64.eq. rewrite Int64.unsigned_repr_eq. rewrite Z.mod_small by exact RANGE.
    rewrite Int64.unsigned_zero. destruct (zeq b 0); cbn; lia.
  - unfold Int64.ltu. rewrite Int64.unsigned_repr_eq. rewrite Z.mod_small by exact RANGE.
    rewrite Int64.unsigned_repr_wordsize.
    change ((if zlt b 64 then true else false) = true <-> b < 64).
    destruct (zlt b 64); cbn; lia.
  - unfold Int64.ltu. rewrite Int64.unsigned_repr_eq. rewrite Z.mod_small by exact RANGE.
    rewrite Int64.unsigned_repr_wordsize.
    change ((if zlt b 64 then true else false) = true <-> b < 64).
    destruct (zlt b 64); cbn; lia.
Qed.

(** Passing the guard rules out semantic failure for every binary operation
    in the emitted u64 fragment.  The result type of comparisons is CompCert's
    [tint]; the direct emitter subsequently casts that result through its u8
    scratch temporary, so this lemma intentionally quantifies over the result
    value instead of claiming that every operation returns a [Vlong]. *)
Theorem sem_binary_operation_u64_defined:
  forall ce m op a b,
  u64_op_defined op b = true ->
  exists v,
    sem_binary_operation ce op (Vlong a) tulong (Vlong b) tulong m = Some v.
Proof.
  intros ce m op a b H.
  destruct Archi.ptr64 eqn:PTR; destruct op; cbv [tulong u64_op_defined sem_binary_operation
    sem_add sem_sub sem_mul sem_div sem_mod
    sem_and sem_or sem_xor sem_shl sem_shr
    sem_shift sem_binarith sem_cast classify_cast classify_binarith binarith_type classify_add classify_sub
    classify_shift typeconv] in H |- *; try rewrite PTR in *;
    try (eexists; reflexivity).
  all: try (destruct (Int64.eq b Int64.zero) eqn:E; cbn in H;
    try discriminate; eexists; reflexivity).
  all: try (rewrite H; eexists; reflexivity).
Qed.

(** Successful execution of a guarded expression is therefore an execution
    in CompCert's real expression semantics, via the generic evaluator
    soundness theorem in [ClightFragmentSem.v].  Whole functions use
    [run_fuel_funcall2], whose conclusion is
    [ClightBigstep.eval_funcall] for the exact emitted Clight AST. *)

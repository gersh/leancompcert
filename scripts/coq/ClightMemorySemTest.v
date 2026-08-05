(* Regression for pointer-indexed array parameters, a full-width store, and a
   load in the memory-aware generic theorem.  This is the Clight shape emitted
   by the production pointer-native array bridge. *)

From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightMemorySem.

Local Open Scope positive_scope.

Definition _base : ident := 1.
Definition _out : ident := 3.
Definition u64ptr : type := Tpointer tulong noattr.

Definition array_cell : expr :=
  Ederef
    (Ebinop Oadd (Etempvar _base u64ptr)
      (Econst_long (Int64.repr 1) tulong) u64ptr)
    tulong.

Definition array_body : statement :=
  Ssequence
    (Sassign array_cell (Econst_long (Int64.repr 7) tulong))
    (Ssequence
      (Sset _out array_cell)
      (Sreturn (Some (Etempvar _out tulong)))).

Definition array_function : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := (_base, u64ptr) :: nil;
  fn_vars := nil;
  fn_temps := (_out, tulong) :: nil;
  fn_body := array_body
|}.

Definition array_ge : genv := {|
  genv_genv := @Genv.empty_genv fundef type nil;
  genv_cenv := PTree.empty composite
|}.

Definition array_ptr (b: block) : val := Vptr b Ptrofs.zero.
Definition array_le0 (b: block) : temp_env :=
  PTree.set _base (array_ptr b)
    (PTree.set _out Vundef (PTree.empty val)).
Definition array_expected : val := Vlong (Int64.repr 7).
Definition array_ofs : Z := Ptrofs.unsigned (Ptrofs.repr 8).

(** Pointer indexing is defined for every [uint64_t] index and scales the
    index by the eight-byte element size. *)
Lemma pointer_index_is_defined : forall ce m b ofs i,
  sem_binary_operation ce Oadd
    (Vptr b ofs) u64ptr (Vlong i) tulong m =
      Some (Vptr b
        (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 i)))).
Proof. reflexivity. Qed.

Corollary pointer_index_one_is_defined : forall ce m b,
  sem_binary_operation ce Oadd
    (Vptr b Ptrofs.zero) u64ptr (Vlong (Int64.repr 1)) tulong m =
      Some (Vptr b (Ptrofs.repr 8)).
Proof.
  intros. rewrite pointer_index_is_defined. reflexivity.
Qed.

Lemma array_bind_parameter : forall b,
  bind_parameter_temps (fn_params array_function) (array_ptr b :: nil)
    (create_undef_temps (fn_temps array_function)) = Some (array_le0 b).
Proof. intros; reflexivity. Qed.

Lemma array_run : forall m b m',
  Mem.store Mint64 m b array_ofs array_expected = Some m' ->
  exists le',
  run_mem_fuel 5 (genv_cenv array_ge) m
    array_body (array_le0 b) =
  Some (le', (m', Out_return (Some (array_expected, tulong)))).
Proof.
  intros m b m' STORE.
  pose proof (Mem.load_store_same Mint64 m b array_ofs array_expected m' STORE)
    as LOAD.
  cbn in LOAD.
  unfold array_body, array_cell, array_le0, array_ptr, array_expected,
    array_ofs, u64ptr, _base, _out in *.
  eexists.
  cbn [run_mem_fuel eval_mem array_ge].
  repeat rewrite PTree.gss.
  repeat (rewrite PTree.gso by congruence).
  rewrite pointer_index_one_is_defined. cbn.
  assert (VALCAST: sem_cast (Vlong (Int64.repr 7)) tulong tulong m =
    Some (Vlong (Int64.repr 7))) by reflexivity.
  rewrite VALCAST. cbn. rewrite STORE. cbn.
  repeat rewrite PTree.gss.
  repeat (rewrite PTree.gso by congruence).
  cbn [sem_add_ptr_long].
  assert (INDEXOFS:
    Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr (sizeof (PTree.empty composite) tulong))
        (Ptrofs.of_int64 (Int64.repr 1))) = Ptrofs.repr 8) by reflexivity.
  rewrite INDEXOFS.
  rewrite LOAD. cbn.
  repeat rewrite PTree.gss.
  repeat (rewrite PTree.gso by congruence).
  reflexivity.
Qed.

Theorem array_funcall : forall m b m',
  Mem.store Mint64 m b array_ofs array_expected = Some m' ->
  ClightBigstep.eval_funcall function_entry2 array_ge m
    (Internal array_function) (array_ptr b :: nil) E0 m' array_expected.
Proof.
  intros m b m' STORE.
  destruct (array_run m b m' STORE) as [le' RUN].
  change (run_mem_fuel 5 (genv_cenv array_ge) m
    (fn_body array_function) (array_le0 b) =
    Some (le', (m', Out_return (Some (array_expected, tulong))))) in RUN.
  eapply run_mem_fuel_funcall2 with
    (fuel := 5%nat) (le0 := array_le0 b) (le' := le')
    (v := array_expected) (ty := tulong).
  - reflexivity.
  - constructor.
    + simpl; tauto.
    + constructor.
  - red; simpl.
    intros x y HX HY HXY.
    destruct HX as [HX|[]].
    destruct HY as [HY|[]].
    subst x. subst y. discriminate.
  - apply array_bind_parameter.
  - discriminate.
  - exact RUN.
  - reflexivity.
Qed.

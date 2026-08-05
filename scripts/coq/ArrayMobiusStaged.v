(** Staged refinement of the exact generated Mobius loop.  This file is
    copied next to the generated [ArrayCheck] module and compiled after it. *)
From compcert Require Import Coqlib Maps Integers Values Events Memory.
From compcert Require Import Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ArrayCert Direct.ClightFlatSem Direct.ArrayCheck.

Definition stage1_atoms := Eval vm_compute in firstn 11 production_loop_atoms.

Definition stage0_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  st.(flat_array) = q.(mob_cells) /\
  PTree.get _v_1 st.(flat_temps) = Some (Vlong q.(mob_pos)) /\
  PTree.get _v_2 st.(flat_temps) = Some (Vlong q.(mob_neg)) /\
  PTree.get _v_3 st.(flat_temps) = Some (Vlong q.(mob_pi)) /\
  PTree.get _v_4 st.(flat_temps) = Some (Vlong q.(mob_p)) /\
  PTree.get _v_5 st.(flat_temps) = Some (Vlong q.(mob_j)) /\
  PTree.get _v_59 st.(flat_temps) = Some (Vlong t) /\
  PTree.get _v_60 st.(flat_temps) = Some (Vptr b Ptrofs.zero).

Definition s1_v6 (t : int64) : int64 :=
  cbit (Int64.ltu t (cI 202298)).
Definition s1_v10 (j : int64) : int64 :=
  cbit (Int64.ltu j (cI 100000)).
Definition s1_v7 (t j : int64) : int64 :=
  Int64.mul (s1_v10 j) (s1_v6 t).
Definition s1_v8 (t j : int64) : int64 :=
  Int64.add (Int64.mul (s1_v7 t j) j)
    (Int64.mul (Int64.sub (cI 1) (s1_v7 t j)) (cI 200000)).
Definition s1_v9 (t j : int64) : int64 :=
  Int64.add (s1_v8 t j) (cI 100000).

Definition stage1_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  stage0_rel b t q st /\
  PTree.get _v_6 st.(flat_temps) = Some (Vlong (s1_v6 t)) /\
  PTree.get _v_7 st.(flat_temps) = Some (Vlong (s1_v7 t q.(mob_j))) /\
  PTree.get _v_8 st.(flat_temps) = Some (Vlong (s1_v8 t q.(mob_j))) /\
  PTree.get _v_9 st.(flat_temps) = Some (Vlong (s1_v9 t q.(mob_j))) /\
  PTree.get _v_14 st.(flat_temps) =
    Some (Vlong (cget q.(mob_cells) (s1_v8 t q.(mob_j)))).

Ltac one_map :=
  first [rewrite PTree.gss | rewrite PTree.gso by
    (unfold _v_1, _v_2, _v_3, _v_4, _v_5, _v_6, _v_7, _v_8,
      _v_9, _v_10, _v_11, _v_12, _v_13, _v_14, _v_15, _v_16,
      _v_17, _v_18, _v_19, _v_20, _v_21, _v_22, _v_23, _v_24,
      _v_25, _v_26, _v_27, _v_28, _v_29, _v_30, _v_31, _v_32,
      _v_33, _v_34, _v_35, _v_36, _v_37, _v_38, _v_39, _v_40,
      _v_41, _v_42, _v_43, _v_44, _v_45, _v_46, _v_47, _v_48,
      _v_49, _v_50, _v_51, _v_52, _v_53, _v_54, _v_55, _v_56,
      _v_57, _v_58, _v_59, _v_60; discriminate)].

Ltac scalar :=
  repeat progress
    (rewrite ?flat_checked_long, ?flat_checked_int, ?flat_checked_uchar,
      ?flat_checked_bool_int, ?flat_checked_bool_uchar,
      ?flat_checked_ptr_u64, ?sem_mul_u64, ?sem_add_u64, ?sem_sub_u64,
      ?sem_lt_u64, ?sem_gt_u64, ?sem_eq_u64, ?sem_ne_u64, ?sem_mod_u64,
      ?sem_xor_u64, ?sem_or_u64, ?sem_and_u64, ?sem_shr_u64,
      ?sem_add_ptr_u64, ?cast_bool_uchar, ?cast_bool_u64, ?cast_u64_u64,
      ?same_block_refl;
     cbn [flat_temps flat_array typeof access_mode andb]).

Theorem stage1_forward : forall b t q st,
  stage0_rel b t q st ->
  cindex_ok (s1_v8 t q.(mob_j)) = true ->
  exists st',
    run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage1_atoms st = Some st' /\
    stage1_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL SAFE.
  cbn [stage0_rel flat_array flat_temps] in REL.
  destruct REL as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = a) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong pi)) in H3.
  change (PTree.get _v_4 le = Some (Vlong p)) in H4.
  change (PTree.get _v_5 le = Some (Vlong j)) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  cbn [stage1_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat];
     repeat rewrite H5; repeat rewrite H59; repeat rewrite H60;
     scalar;
     repeat progress (one_map; scalar)).
  repeat rewrite H5. repeat rewrite H59. repeat rewrite H60.
  scalar.
  repeat progress (one_map; scalar).
  unfold cindex_ok, cbyte_offset, s1_v8, s1_v7, s1_v10, s1_v6 in SAFE.
  lazymatch goal with
  | |- context [if ?actual then _ else _] =>
      lazymatch type of SAFE with ?expected = true =>
        assert (E : actual = expected) by
          (unfold flat_offset_ok, cbit, cI; f_equal)
      end
  end.
  rewrite E, SAFE. scalar.
  fold _v_6 _v_7 _v_8 _v_9 _v_10 _v_11 _v_12 _v_13 _v_14 in *.
  eexists. split; [reflexivity|].
  cbn [stage1_rel stage0_rel flat_temps flat_array s1_v6 s1_v7
    s1_v8 s1_v9 s1_v10 cget].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H59 | rewrite H60 | scalar];
    try reflexivity; try assumption.
Qed.

(* Defined below stage 3; this first prototype copy is retained as a comment
   while the staged script is being assembled. *)
(**
Definition stage4_atoms := Eval vm_compute in
  firstn 11 (skipn 25 production_loop_atoms).
Definition s4_v25 (t j : int64) : int64 :=
  Int64.sub (cI 1) (s1_v7 t j).
Definition s4_v26 (t j : int64) : int64 :=
  Int64.mul (s1_v6 t) (s4_v25 t j).
Definition s4_v27 (t pi j : int64) : int64 :=
  Int64.add pi (s4_v26 t j).
Definition s4_v28 (t pi j : int64) : int64 :=
  cbit (Int64.ltu (cI 65) (s4_v27 t pi j)).
Definition s4_v29 (t pi j : int64) : int64 :=
  Int64.sub (cI 1) (s4_v28 t pi j).
Definition s4_v30 (t pi j : int64) : int64 :=
  Int64.mul (s4_v29 t pi j) (s4_v27 t pi j).
Definition s4_v31 (t pi j : int64) : int64 :=
  Int64.mul (s4_v28 t pi j) (cI 65).
Definition s4_pi (t pi j : int64) : int64 :=
  Int64.add (s4_v30 t pi j) (s4_v31 t pi j).
Definition s4_v32 (t pi j : int64) : int64 :=
  Int64.add (s4_pi t pi j) (cI 300001).
Definition s4_v33 (a : compact_cells) (t pi p j : int64) : int64 :=
  cget (s3_a2 a t p j) (s4_v32 t pi j).

Definition stage4_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  core_rel b t (s3_a2 q.(mob_cells) t q.(mob_p) q.(mob_j))
    q.(mob_pos) q.(mob_neg) (s4_pi t q.(mob_pi) q.(mob_j))
    q.(mob_p) q.(mob_j) st /\
  PTree.get _v_6 st.(flat_temps) = Some (Vlong (s1_v6 t)) /\
  PTree.get _v_26 st.(flat_temps) =
    Some (Vlong (s4_v26 t q.(mob_j))) /\
  PTree.get _v_33 st.(flat_temps) =
    Some (Vlong (s4_v33 q.(mob_cells) t q.(mob_pi)
      q.(mob_p) q.(mob_j))).

Theorem stage4_forward : forall b t q st,
  stage3_rel b t q st ->
  cindex_ok (s4_v32 t q.(mob_pi) q.(mob_j)) = true ->
  exists st',
    run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage4_atoms st = Some st' /\
    stage4_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL SAFE32.
  cbn [stage3_rel] in REL.
  destruct REL as [BASE [H6 H7]].
  cbn [flat_temps flat_array] in H6, H7.
  cbn [core_rel flat_array flat_temps] in BASE.
  destruct BASE as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = s3_a2 a t p j) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong pi)) in H3.
  change (PTree.get _v_4 le = Some (Vlong p)) in H4.
  change (PTree.get _v_5 le = Some (Vlong j)) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  cbn [stage4_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_6 _v_7 _v_25 _v_26 _v_27
    _v_28 _v_29 _v_30 _v_31 _v_32 _v_33 _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat];
     repeat rewrite H3; repeat rewrite H6; repeat rewrite H7;
     repeat rewrite H60; scalar;
     repeat progress (one_map; scalar)).
  unfold cindex_ok, cbyte_offset, s4_v32, s4_pi, s4_v31, s4_v30,
    s4_v29, s4_v28, s4_v27, s4_v26, s4_v25, s1_v7, s1_v10,
    s1_v6 in SAFE32.
  lazymatch goal with
  | |- context [if ?actual then _ else _] =>
      lazymatch type of SAFE32 with ?expected = true =>
        assert (OFFSET32 : actual = expected) by
          (unfold flat_offset_ok, cI, cbit; cbn; f_equal)
      end
  end.
  rewrite OFFSET32, SAFE32. scalar.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat]; scalar;
     repeat progress (one_map; scalar)).
  eexists. split; [reflexivity|].
  cbn [stage4_rel core_rel flat_temps flat_array s4_v33 s4_v32 s4_pi
    s4_v31 s4_v30 s4_v29 s4_v28 s4_v27 s4_v26 s4_v25 s3_a2
    s3_v24 s3_v23 s3_v22 s3_v21 s3_v20 s3_v19 s2_v18 s2_a1
    s2_v17 s2_v16 s2_v15 s2_v14 s1_v6 s1_v7 s1_v8 s1_v9 cget cset].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H6 | rewrite H7 | rewrite H59 |
      rewrite H60 | scalar];
    try reflexivity; try assumption. (* inactive prototype copy *)
Qed.

Definition stage5_atoms := Eval vm_compute in
  firstn 13 (skipn 36 production_loop_atoms).
Definition s5_v34 (t j : int64) : int64 :=
  Int64.sub (cI 1) (s4_v26 t j).
Definition s5_v35 (p j : int64) : int64 := Int64.add j p.
Definition s5_v36 (a : compact_cells) (t pi p j : int64) : int64 :=
  Int64.mul (s4_v26 t j) (s4_v33 a t pi p j).
Definition s5_v37 (t p j : int64) : int64 :=
  Int64.mul (s5_v34 t j) p.
Definition s5_p (a : compact_cells) (t pi p j : int64) : int64 :=
  Int64.add (s5_v36 a t pi p j) (s5_v37 t p j).
Definition s5_v38 (a : compact_cells) (t pi p j : int64) : int64 :=
  Int64.mul (s4_v26 t j) (s5_p a t pi p j).
Definition s5_v39 (t p j : int64) : int64 :=
  Int64.mul (s5_v34 t j) (s5_v35 p j).
Definition s5_j (a : compact_cells) (t pi p j : int64) : int64 :=
  Int64.add (s5_v38 a t pi p j) (s5_v39 t p j).
Definition s5_v40 (t : int64) : int64 := Int64.sub t (cI 202298).
Definition s5_v41 (t : int64) : int64 := Int64.sub (cI 1) (s1_v6 t).
Definition s5_v42 (t : int64) : int64 :=
  Int64.mul (s5_v41 t) (s5_v40 t).
Definition s5_v43 (t : int64) : int64 := Int64.add (s5_v42 t) (cI 100000).
Definition s5_v44 (a : compact_cells) (t p j : int64) : int64 :=
  cget (s3_a2 a t p j) (s5_v42 t).

Definition stage5_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  core_rel b t (s3_a2 q.(mob_cells) t q.(mob_p) q.(mob_j))
    q.(mob_pos) q.(mob_neg) (s4_pi t q.(mob_pi) q.(mob_j))
    (s5_p q.(mob_cells) t q.(mob_pi) q.(mob_p) q.(mob_j))
    (s5_j q.(mob_cells) t q.(mob_pi) q.(mob_p) q.(mob_j)) st /\
  PTree.get _v_41 st.(flat_temps) = Some (Vlong (s5_v41 t)) /\
  PTree.get _v_42 st.(flat_temps) = Some (Vlong (s5_v42 t)) /\
  PTree.get _v_43 st.(flat_temps) = Some (Vlong (s5_v43 t)) /\
  PTree.get _v_44 st.(flat_temps) =
    Some (Vlong (s5_v44 q.(mob_cells) t q.(mob_p) q.(mob_j))).

Theorem stage5_forward : forall b t q st,
  stage4_rel b t q st ->
  cindex_ok (s5_v42 t) = true ->
  exists st',
    run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage5_atoms st = Some st' /\
    stage5_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL SAFE42.
  cbn [stage4_rel] in REL.
  destruct REL as [BASE [H6 [H26 H33]]].
  cbn [flat_temps flat_array] in H6, H26, H33.
  cbn [core_rel flat_array flat_temps] in BASE.
  destruct BASE as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = s3_a2 a t p j) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong (s4_pi t pi j))) in H3.
  change (PTree.get _v_4 le = Some (Vlong p)) in H4.
  change (PTree.get _v_5 le = Some (Vlong j)) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  cbn [stage5_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_6 _v_26 _v_33 _v_34 _v_35
    _v_36 _v_37 _v_38 _v_39 _v_40 _v_41 _v_42 _v_43 _v_44
    _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat];
     repeat rewrite H4; repeat rewrite H5; repeat rewrite H6;
     repeat rewrite H26; repeat rewrite H33; repeat rewrite H59;
     repeat rewrite H60; scalar;
     repeat progress (one_map; scalar)).
  unfold cindex_ok, cbyte_offset, s5_v42, s5_v41, s5_v40, s1_v6 in SAFE42.
  lazymatch goal with
  | |- context [if ?actual then _ else _] =>
      lazymatch type of SAFE42 with ?expected = true =>
        assert (OFFSET42 : actual = expected) by
          (unfold flat_offset_ok, cI, cbit; cbn; f_equal)
      end
  end.
  rewrite OFFSET42, SAFE42. scalar.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat]; scalar;
     repeat progress (one_map; scalar)).
  eexists. split; [reflexivity|].
  cbn [stage5_rel core_rel flat_temps flat_array s5_v44 s5_v43 s5_v42
    s5_v41 s5_v40 s5_j s5_v39 s5_v38 s5_p s5_v37 s5_v36 s5_v35
    s5_v34 s4_v33 s4_v32 s4_pi s4_v31 s4_v30 s4_v29 s4_v28
    s4_v27 s4_v26 s4_v25 s3_a2 s3_v24 s3_v23 s3_v22 s3_v21
    s3_v20 s3_v19 s2_v18 s2_a1 s2_v17 s2_v16 s2_v15 s2_v14
    s1_v6 s1_v7 s1_v8 s1_v9 cget cset].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H6 | rewrite H26 | rewrite H33 |
      rewrite H59 | rewrite H60 | scalar];
    try reflexivity; try assumption. (* inactive stage5 copy *)
Qed.
*)

Definition stage2_atoms := Eval vm_compute in
  firstn 6 (skipn 11 production_loop_atoms).

Definition s2_v14 (a : compact_cells) (t j : int64) : int64 :=
  cget a (s1_v8 t j).
Definition s2_v15 (a : compact_cells) (t j : int64) : int64 :=
  cbit (Int64.eq (s2_v14 a t j) (cI 0)).
Definition s2_v16 (a : compact_cells) (t j : int64) : int64 :=
  Int64.add (s2_v14 a t j) (s2_v15 a t j).
Definition s2_v17 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.mul (s2_v16 a t j) p.
Definition s2_a1 (a : compact_cells) (t p j : int64) : compact_cells :=
  cset a (s1_v8 t j) (s2_v17 a t p j).
Definition s2_v18 (a : compact_cells) (t p j : int64) : int64 :=
  cget (s2_a1 a t p j) (s1_v9 t j).

Definition core_rel (b : block) (t : int64) (a : compact_cells)
    (pos neg pi p j : int64) (st : flat_state) : Prop :=
  st.(flat_array) = a /\
  PTree.get _v_1 st.(flat_temps) = Some (Vlong pos) /\
  PTree.get _v_2 st.(flat_temps) = Some (Vlong neg) /\
  PTree.get _v_3 st.(flat_temps) = Some (Vlong pi) /\
  PTree.get _v_4 st.(flat_temps) = Some (Vlong p) /\
  PTree.get _v_5 st.(flat_temps) = Some (Vlong j) /\
  PTree.get _v_59 st.(flat_temps) = Some (Vlong t) /\
  PTree.get _v_60 st.(flat_temps) = Some (Vptr b Ptrofs.zero).

Definition stage2_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  core_rel b t (s2_a1 q.(mob_cells) t q.(mob_p) q.(mob_j))
    q.(mob_pos) q.(mob_neg) q.(mob_pi) q.(mob_p) q.(mob_j) st /\
  PTree.get _v_6 st.(flat_temps) = Some (Vlong (s1_v6 t)) /\
  PTree.get _v_7 st.(flat_temps) = Some (Vlong (s1_v7 t q.(mob_j))) /\
  PTree.get _v_8 st.(flat_temps) = Some (Vlong (s1_v8 t q.(mob_j))) /\
  PTree.get _v_9 st.(flat_temps) = Some (Vlong (s1_v9 t q.(mob_j))) /\
  PTree.get _v_18 st.(flat_temps) =
    Some (Vlong (s2_v18 q.(mob_cells) t q.(mob_p) q.(mob_j))).

Ltac offset_step SAFE :=
  lazymatch goal with
  | |- context [if ?actual then _ else _] =>
      lazymatch type of SAFE with ?expected = true =>
        let E := fresh "OFFSET" in
        assert (E : actual = expected) by
          (unfold flat_offset_ok, cindex_ok, cbyte_offset, s1_v9, s1_v8,
             s1_v7, s1_v10, s1_v6, cbit, cI; cbn; f_equal);
        rewrite E, SAFE; scalar
      end
  end.

Theorem stage2_forward : forall b t q st,
  stage1_rel b t q st ->
  cindex_ok (s1_v8 t q.(mob_j)) = true ->
  cindex_ok (s1_v9 t q.(mob_j)) = true ->
  exists st',
    run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage2_atoms st = Some st' /\
    stage2_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL SAFE8 SAFE9.
  cbn [stage1_rel] in REL.
  destruct REL as [BASE [H6 [H7 [H8 [H9 H14]]]]].
  cbn [flat_temps flat_array] in H6, H7, H8, H9, H14.
  cbn [stage0_rel flat_array flat_temps] in BASE.
  destruct BASE as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = a) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong pi)) in H3.
  change (PTree.get _v_4 le = Some (Vlong p)) in H4.
  change (PTree.get _v_5 le = Some (Vlong j)) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  cbn [stage2_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_6 _v_7 _v_8 _v_9 _v_14
    _v_15 _v_16 _v_17 _v_18 _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat];
     repeat rewrite H4; repeat rewrite H6; repeat rewrite H7;
     repeat rewrite H8; repeat rewrite H9; repeat rewrite H14;
     repeat rewrite H60; scalar;
     repeat progress (one_map; scalar)).
  unfold cindex_ok, cbyte_offset, s1_v8, s1_v7, s1_v10, s1_v6 in SAFE8.
  offset_step SAFE8.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat];
     repeat rewrite H4; repeat rewrite H6; repeat rewrite H7;
     repeat rewrite H8; repeat rewrite H9; repeat rewrite H14;
     repeat rewrite H60; scalar;
     repeat progress (one_map; scalar)).
  unfold cindex_ok, cbyte_offset, s1_v9, s1_v8, s1_v7, s1_v10,
    s1_v6 in SAFE9.
  offset_step SAFE9.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat]; scalar;
     repeat progress (one_map; scalar)).
  fold _v_15 _v_16 _v_17 _v_18 in *.
  eexists. split; [reflexivity|].
  cbn [stage2_rel core_rel flat_temps flat_array s2_a1 s2_v17 s2_v16
    s2_v15 s2_v14 s2_v18 s1_v6 s1_v7 s1_v8 s1_v9 cget cset].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H6 | rewrite H7 | rewrite H8 |
      rewrite H9 | rewrite H14 | rewrite H59 | rewrite H60 | scalar];
    try reflexivity; try assumption.
Qed.

Definition stage3_atoms := Eval vm_compute in
  firstn 8 (skipn 17 production_loop_atoms).
Definition s3_v19 (p : int64) : int64 := Int64.mul p p.
Definition s3_v20 (t p j : int64) : int64 :=
  Int64.modu (s1_v8 t j) (s3_v19 p).
Definition s3_v21 (t p j : int64) : int64 :=
  cbit (Int64.eq (s3_v20 t p j) (cI 0)).
Definition s3_v22 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.xor (s2_v18 a t p j) (cI 1).
Definition s3_v23 (t p j : int64) : int64 :=
  Int64.mul (s3_v21 t p j) (cI 2).
Definition s3_v24 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.or (s3_v22 a t p j) (s3_v23 t p j).
Definition s3_a2 (a : compact_cells) (t p j : int64) : compact_cells :=
  cset (s2_a1 a t p j) (s1_v9 t j) (s3_v24 a t p j).

Definition stage3_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  core_rel b t (s3_a2 q.(mob_cells) t q.(mob_p) q.(mob_j))
    q.(mob_pos) q.(mob_neg) q.(mob_pi) q.(mob_p) q.(mob_j) st /\
  PTree.get _v_6 st.(flat_temps) = Some (Vlong (s1_v6 t)) /\
  PTree.get _v_7 st.(flat_temps) = Some (Vlong (s1_v7 t q.(mob_j))).

Theorem stage3_forward : forall b t q st,
  stage2_rel b t q st ->
  cindex_ok (s1_v9 t q.(mob_j)) = true ->
  negb (Int64.eq (s3_v19 q.(mob_p)) (cI 0)) = true ->
  exists st',
    run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage3_atoms st = Some st' /\
    stage3_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL SAFE9 NZ.
  cbn [stage2_rel] in REL.
  destruct REL as [BASE [H6 [H7 [H8 [H9 H18]]]]].
  cbn [flat_temps flat_array] in H6, H7, H8, H9, H18.
  cbn [core_rel flat_array flat_temps] in BASE.
  destruct BASE as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = s2_a1 a t p j) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong pi)) in H3.
  change (PTree.get _v_4 le = Some (Vlong p)) in H4.
  change (PTree.get _v_5 le = Some (Vlong j)) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  apply Bool.negb_true_iff in NZ.
  change (Int64.eq (Int64.mul p p) Int64.zero = false) in NZ.
  cbn [stage3_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_6 _v_7 _v_8 _v_9 _v_18 _v_19
    _v_20 _v_21 _v_22 _v_23 _v_24 _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat];
     repeat rewrite H4; repeat rewrite H6; repeat rewrite H7;
     repeat rewrite H8; repeat rewrite H9; repeat rewrite H18; repeat rewrite H60;
     scalar; try rewrite NZ; scalar;
     repeat progress (one_map; scalar; try rewrite NZ; scalar)).
  unfold cindex_ok, cbyte_offset, s1_v9, s1_v8, s1_v7, s1_v10,
    s1_v6 in SAFE9.
  offset_step SAFE9.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat]; scalar;
     repeat progress (one_map; scalar)).
  eexists. split; [reflexivity|].
  cbn [stage3_rel core_rel flat_temps flat_array s3_a2 s3_v24 s3_v23
    s3_v22 s3_v21 s3_v20 s3_v19 s2_v18 s2_a1 s2_v17 s2_v16
    s2_v15 s2_v14 s1_v6 s1_v7 s1_v8 s1_v9 cget cset].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H6 | rewrite H7 | rewrite H8 | rewrite H9 |
      rewrite H18 | rewrite H59 | rewrite H60 | rewrite NZ | scalar];
    try reflexivity; try assumption.
  all: reflexivity.
Qed.

Definition stage4_atoms := Eval vm_compute in
  firstn 11 (skipn 25 production_loop_atoms).
Definition s4_v25 (t j : int64) : int64 :=
  Int64.sub (cI 1) (s1_v7 t j).
Definition s4_v26 (t j : int64) : int64 :=
  Int64.mul (s1_v6 t) (s4_v25 t j).
Definition s4_v27 (t pi j : int64) : int64 :=
  Int64.add pi (s4_v26 t j).
Definition s4_v28 (t pi j : int64) : int64 :=
  cbit (Int64.ltu (cI 65) (s4_v27 t pi j)).
Definition s4_v29 (t pi j : int64) : int64 :=
  Int64.sub (cI 1) (s4_v28 t pi j).
Definition s4_v30 (t pi j : int64) : int64 :=
  Int64.mul (s4_v29 t pi j) (s4_v27 t pi j).
Definition s4_v31 (t pi j : int64) : int64 :=
  Int64.mul (s4_v28 t pi j) (cI 65).
Definition s4_pi (t pi j : int64) : int64 :=
  Int64.add (s4_v30 t pi j) (s4_v31 t pi j).
Definition s4_v32 (t pi j : int64) : int64 :=
  Int64.add (s4_pi t pi j) (cI 300001).
Definition s4_v33 (a : compact_cells) (t pi p j : int64) : int64 :=
  cget (s3_a2 a t p j) (s4_v32 t pi j).

Definition stage4_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  core_rel b t (s3_a2 q.(mob_cells) t q.(mob_p) q.(mob_j))
    q.(mob_pos) q.(mob_neg) (s4_pi t q.(mob_pi) q.(mob_j))
    q.(mob_p) q.(mob_j) st /\
  PTree.get _v_6 st.(flat_temps) = Some (Vlong (s1_v6 t)) /\
  PTree.get _v_26 st.(flat_temps) =
    Some (Vlong (s4_v26 t q.(mob_j))) /\
  PTree.get _v_33 st.(flat_temps) =
    Some (Vlong (s4_v33 q.(mob_cells) t q.(mob_pi)
      q.(mob_p) q.(mob_j))).

Theorem stage4_forward : forall b t q st,
  stage3_rel b t q st ->
  cindex_ok (s4_v32 t q.(mob_pi) q.(mob_j)) = true ->
  exists st',
    run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage4_atoms st = Some st' /\
    stage4_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL SAFE32.
  cbn [stage3_rel] in REL.
  destruct REL as [BASE [H6 H7]].
  cbn [flat_temps flat_array] in H6, H7.
  cbn [core_rel flat_array flat_temps] in BASE.
  destruct BASE as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = s3_a2 a t p j) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong pi)) in H3.
  change (PTree.get _v_4 le = Some (Vlong p)) in H4.
  change (PTree.get _v_5 le = Some (Vlong j)) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  cbn [stage4_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_6 _v_7 _v_25 _v_26 _v_27
    _v_28 _v_29 _v_30 _v_31 _v_32 _v_33 _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat];
     repeat rewrite H3; repeat rewrite H6; repeat rewrite H7;
     repeat rewrite H60; scalar;
     repeat progress (one_map; scalar)).
  unfold cindex_ok, cbyte_offset, s4_v32, s4_pi, s4_v31, s4_v30,
    s4_v29, s4_v28, s4_v27, s4_v26, s4_v25, s1_v7, s1_v10,
    s1_v6 in SAFE32.
  lazymatch goal with
  | |- context [if ?actual then _ else _] =>
      lazymatch type of SAFE32 with ?expected = true =>
        assert (OFFSET32 : actual = expected) by
          (unfold flat_offset_ok, cI, cbit; cbn; f_equal)
      end
  end.
  rewrite OFFSET32, SAFE32. scalar.
  repeat progress
    (try unfold run_flat_atom at 1;
     cbn [run_flat_fuel eval_flat]; scalar;
     repeat progress (one_map; scalar)).
  eexists. split; [reflexivity|].
  cbn [stage4_rel core_rel flat_temps flat_array s4_v33 s4_v32 s4_pi
    s4_v31 s4_v30 s4_v29 s4_v28 s4_v27 s4_v26 s4_v25 s3_a2
    s3_v24 s3_v23 s3_v22 s3_v21 s3_v20 s3_v19 s2_v18 s2_a1
    s2_v17 s2_v16 s2_v15 s2_v14 s1_v6 s1_v7 s1_v8 s1_v9 cget cset].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H6 | rewrite H7 | rewrite H59 |
      rewrite H60 | scalar];
    try reflexivity; try assumption.
Qed.

Definition stage5_atoms := Eval vm_compute in
  firstn 13 (skipn 36 production_loop_atoms).
Definition s5_v34 (t j : int64) : int64 := Int64.sub (cI 1) (s4_v26 t j).
Definition s5_v35 (p j : int64) : int64 := Int64.add j p.
Definition s5_v36 (a : compact_cells) (t pi p j : int64) : int64 :=
  Int64.mul (s4_v26 t j) (s4_v33 a t pi p j).
Definition s5_v37 (t p j : int64) : int64 := Int64.mul (s5_v34 t j) p.
Definition s5_p (a : compact_cells) (t pi p j : int64) : int64 :=
  Int64.add (s5_v36 a t pi p j) (s5_v37 t p j).
Definition s5_v38 (a : compact_cells) (t pi p j : int64) : int64 :=
  Int64.mul (s4_v26 t j) (s5_p a t pi p j).
Definition s5_v39 (t p j : int64) : int64 :=
  Int64.mul (s5_v34 t j) (s5_v35 p j).
Definition s5_j (a : compact_cells) (t pi p j : int64) : int64 :=
  Int64.add (s5_v38 a t pi p j) (s5_v39 t p j).
Definition s5_v40 (t : int64) : int64 := Int64.sub t (cI 202298).
Definition s5_v41 (t : int64) : int64 := Int64.sub (cI 1) (s1_v6 t).
Definition s5_v42 (t : int64) : int64 := Int64.mul (s5_v41 t) (s5_v40 t).
Definition s5_v43 (t : int64) : int64 := Int64.add (s5_v42 t) (cI 100000).
Definition s5_v44 (a : compact_cells) (t p j : int64) : int64 :=
  cget (s3_a2 a t p j) (s5_v42 t).

Definition stage5_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  core_rel b t (s3_a2 q.(mob_cells) t q.(mob_p) q.(mob_j))
    q.(mob_pos) q.(mob_neg) (s4_pi t q.(mob_pi) q.(mob_j))
    (s5_p q.(mob_cells) t q.(mob_pi) q.(mob_p) q.(mob_j))
    (s5_j q.(mob_cells) t q.(mob_pi) q.(mob_p) q.(mob_j)) st /\
  PTree.get _v_41 st.(flat_temps) = Some (Vlong (s5_v41 t)) /\
  PTree.get _v_42 st.(flat_temps) = Some (Vlong (s5_v42 t)) /\
  PTree.get _v_43 st.(flat_temps) = Some (Vlong (s5_v43 t)) /\
  PTree.get _v_44 st.(flat_temps) =
    Some (Vlong (s5_v44 q.(mob_cells) t q.(mob_p) q.(mob_j))).

Theorem stage5_forward : forall b t q st,
  stage4_rel b t q st -> cindex_ok (s5_v42 t) = true ->
  exists st', run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage5_atoms st = Some st' /\ stage5_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL SAFE42.
  cbn [stage4_rel] in REL. destruct REL as [BASE [H6 [H26 H33]]].
  cbn [flat_temps flat_array] in H6, H26, H33.
  cbn [core_rel flat_array flat_temps] in BASE.
  destruct BASE as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = s3_a2 a t p j) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong (s4_pi t pi j))) in H3.
  change (PTree.get _v_4 le = Some (Vlong p)) in H4.
  change (PTree.get _v_5 le = Some (Vlong j)) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  cbn [stage5_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_6 _v_26 _v_33 _v_34 _v_35
    _v_36 _v_37 _v_38 _v_39 _v_40 _v_41 _v_42 _v_43 _v_44 _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1; cbn [run_flat_fuel eval_flat];
     repeat rewrite H4; repeat rewrite H5; repeat rewrite H6;
     repeat rewrite H26; repeat rewrite H33; repeat rewrite H59;
     repeat rewrite H60; scalar; repeat progress (one_map; scalar)).
  unfold cindex_ok, cbyte_offset, s5_v42, s5_v41, s5_v40, s1_v6 in SAFE42.
  lazymatch goal with
  | |- context [if ?actual then _ else _] =>
      lazymatch type of SAFE42 with ?expected = true =>
        assert (OFFSET42 : actual = expected) by
          (unfold flat_offset_ok, cI, cbit; cbn; f_equal)
      end
  end.
  rewrite OFFSET42, SAFE42. scalar.
  repeat progress
    (try unfold run_flat_atom at 1; cbn [run_flat_fuel eval_flat]; scalar;
     repeat progress (one_map; scalar)).
  eexists. split; [reflexivity|].
  cbn [stage5_rel core_rel flat_temps flat_array s5_v44 s5_v43 s5_v42
    s5_v41 s5_v40 s5_j s5_v39 s5_v38 s5_p s5_v37 s5_v36 s5_v35
    s5_v34 s4_v33 s4_v32 s4_pi s4_v31 s4_v30 s4_v29 s4_v28
    s4_v27 s4_v26 s4_v25 s3_a2 s3_v24 s3_v23 s3_v22 s3_v21
    s3_v20 s3_v19 s2_v18 s2_a1 s2_v17 s2_v16 s2_v15 s2_v14
    s1_v6 s1_v7 s1_v8 s1_v9 cget cset].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H6 | rewrite H26 | rewrite H33 |
      rewrite H59 | rewrite H60 | scalar]; try reflexivity; try assumption.
Qed.

Definition stage6_atoms := Eval vm_compute in
  firstn 4 (skipn 49 production_loop_atoms).
Definition s6_v45 (a : compact_cells) (t p j : int64) : int64 :=
  cbit (Int64.eq (s5_v44 a t p j) (cI 0)).
Definition s6_v46 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.add (s5_v44 a t p j) (s6_v45 a t p j).
Definition s6_v47 (a : compact_cells) (t p j : int64) : int64 :=
  cget (s3_a2 a t p j) (s5_v43 t).

Definition stage6_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  core_rel b t (s3_a2 q.(mob_cells) t q.(mob_p) q.(mob_j))
    q.(mob_pos) q.(mob_neg) (s4_pi t q.(mob_pi) q.(mob_j))
    (s5_p q.(mob_cells) t q.(mob_pi) q.(mob_p) q.(mob_j))
    (s5_j q.(mob_cells) t q.(mob_pi) q.(mob_p) q.(mob_j)) st /\
  PTree.get _v_41 st.(flat_temps) = Some (Vlong (s5_v41 t)) /\
  PTree.get _v_42 st.(flat_temps) = Some (Vlong (s5_v42 t)) /\
  PTree.get _v_46 st.(flat_temps) =
    Some (Vlong (s6_v46 q.(mob_cells) t q.(mob_p) q.(mob_j))) /\
  PTree.get _v_47 st.(flat_temps) =
    Some (Vlong (s6_v47 q.(mob_cells) t q.(mob_p) q.(mob_j))).

Theorem stage6_forward : forall b t q st,
  stage5_rel b t q st -> cindex_ok (s5_v43 t) = true ->
  exists st', run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage6_atoms st = Some st' /\ stage6_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL SAFE43.
  cbn [stage5_rel] in REL.
  destruct REL as [BASE [H41 [H42 [H43 H44]]]].
  cbn [flat_temps flat_array] in H41, H42, H43, H44.
  cbn [core_rel flat_array flat_temps] in BASE.
  destruct BASE as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = s3_a2 a t p j) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong (s4_pi t pi j))) in H3.
  change (PTree.get _v_4 le = Some (Vlong (s5_p a t pi p j))) in H4.
  change (PTree.get _v_5 le = Some (Vlong (s5_j a t pi p j))) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  cbn [stage6_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_41 _v_42 _v_43 _v_44 _v_45
    _v_46 _v_47 _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1; cbn [run_flat_fuel eval_flat];
     repeat rewrite H43; repeat rewrite H44; repeat rewrite H60;
     scalar; repeat progress (one_map; scalar)).
  unfold cindex_ok, cbyte_offset, s5_v43, s5_v42, s5_v41, s5_v40,
    s1_v6 in SAFE43.
  lazymatch goal with
  | |- context [if ?actual then _ else _] =>
      lazymatch type of SAFE43 with ?expected = true =>
        assert (OFFSET43 : actual = expected) by
          (unfold flat_offset_ok, cI, cbit; cbn; f_equal)
      end
  end.
  rewrite OFFSET43, SAFE43. scalar.
  repeat progress
    (try unfold run_flat_atom at 1; cbn [run_flat_fuel eval_flat]; scalar;
     repeat progress (one_map; scalar)).
  eexists. split; [reflexivity|].
  cbn [stage6_rel core_rel flat_temps flat_array s6_v47 s6_v46 s6_v45
    s5_v44 s5_v43 s5_v42 s5_v41 s5_v40 s5_j s5_v39 s5_v38 s5_p
    s5_v37 s5_v36 s5_v35 s5_v34 s4_v33 s4_v32 s4_pi s4_v31
    s4_v30 s4_v29 s4_v28 s4_v27 s4_v26 s4_v25 s3_a2 s3_v24
    s3_v23 s3_v22 s3_v21 s3_v20 s3_v19 s2_v18 s2_a1 s2_v17
    s2_v16 s2_v15 s2_v14 s1_v6 s1_v7 s1_v8 s1_v9 cget cset].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H41 | rewrite H42 | rewrite H43 |
      rewrite H44 | rewrite H59 | rewrite H60 | scalar];
    try reflexivity; try assumption.
Qed.

Definition stage7_atoms := Eval vm_compute in
  firstn 15 (skipn 53 production_loop_atoms).
Definition s7_v48 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.shru (s6_v47 a t p j) (cI 1).
Definition s7_v49 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.and (s7_v48 a t p j) (cI 1).
Definition s7_v50 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.and (s6_v47 a t p j) (cI 1).
Definition s7_v51 (a : compact_cells) (t p j : int64) : int64 :=
  cbit (negb (Int64.eq (s6_v46 a t p j) (s5_v42 t))).
Definition s7_v52 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.xor (s7_v50 a t p j) (s7_v51 a t p j).
Definition s7_v53 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.sub (cI 1) (s7_v49 a t p j).
Definition s7_v54 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.sub (cI 1) (s7_v52 a t p j).
Definition s7_v55 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.mul (s7_v53 a t p j) (s7_v54 a t p j).
Definition s7_v56 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.mul (s7_v53 a t p j) (s7_v52 a t p j).
Definition s7_v57 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.mul (s5_v41 t) (s7_v55 a t p j).
Definition s7_v58 (a : compact_cells) (t p j : int64) : int64 :=
  Int64.mul (s5_v41 t) (s7_v56 a t p j).
Definition s7_pos (a : compact_cells) (t pos p j : int64) : int64 :=
  Int64.add pos (s7_v57 a t p j).
Definition s7_neg (a : compact_cells) (t neg p j : int64) : int64 :=
  Int64.add neg (s7_v58 a t p j).

Definition stage7_rel (b : block) (t : int64) (q : mob_state)
    (st : flat_state) : Prop :=
  core_rel b (Int64.add t (cI 1))
    (s3_a2 q.(mob_cells) t q.(mob_p) q.(mob_j))
    (s7_pos q.(mob_cells) t q.(mob_pos) q.(mob_p) q.(mob_j))
    (s7_neg q.(mob_cells) t q.(mob_neg) q.(mob_p) q.(mob_j))
    (s4_pi t q.(mob_pi) q.(mob_j))
    (s5_p q.(mob_cells) t q.(mob_pi) q.(mob_p) q.(mob_j))
    (s5_j q.(mob_cells) t q.(mob_pi) q.(mob_p) q.(mob_j)) st.

Theorem stage7_forward : forall b t q st,
  stage6_rel b t q st ->
  exists st', run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      stage7_atoms st = Some st' /\ stage7_rel b t q st'.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL.
  cbn [stage6_rel] in REL.
  destruct REL as [BASE [H41 [H42 [H46 H47]]]].
  cbn [flat_temps flat_array] in H41, H42, H46, H47.
  cbn [core_rel flat_array flat_temps] in BASE.
  destruct BASE as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (cells = s3_a2 a t p j) in HA. subst cells.
  change (PTree.get _v_1 le = Some (Vlong pos)) in H1.
  change (PTree.get _v_2 le = Some (Vlong neg)) in H2.
  change (PTree.get _v_3 le = Some (Vlong (s4_pi t pi j))) in H3.
  change (PTree.get _v_4 le = Some (Vlong (s5_p a t pi p j))) in H4.
  change (PTree.get _v_5 le = Some (Vlong (s5_j a t pi p j))) in H5.
  change (PTree.get _v_59 le = Some (Vlong t)) in H59.
  change (PTree.get _v_60 le = Some (Vptr b Ptrofs.zero)) in H60.
  assert (SHIFTRANGE : Int64.ltu (cI 1) (Int64.repr 64) = true) by
    (vm_compute; reflexivity).
  cbn [stage7_atoms run_flat_atoms].
  fold _v_1 _v_2 _v_3 _v_4 _v_5 _v_41 _v_42 _v_46 _v_47 _v_48
    _v_49 _v_50 _v_51 _v_52 _v_53 _v_54 _v_55 _v_56 _v_57 _v_58
    _v_59 _v_60 in *.
  repeat progress
    (try unfold run_flat_atom at 1; cbn [run_flat_fuel eval_flat];
     repeat rewrite H1; repeat rewrite H2; repeat rewrite H41;
     repeat rewrite H42; repeat rewrite H46; repeat rewrite H47;
     repeat rewrite H59;
     scalar; try rewrite SHIFTRANGE; scalar;
     repeat progress (one_map; scalar; try rewrite SHIFTRANGE; scalar)).
  eexists. split; [reflexivity|].
  cbn [stage7_rel core_rel flat_temps flat_array s7_neg s7_pos s7_v58
    s7_v57 s7_v56 s7_v55 s7_v54 s7_v53 s7_v52 s7_v51 s7_v50
    s7_v49 s7_v48 s6_v47 s6_v46 s6_v45 s5_v44 s5_v43 s5_v42
    s5_v41 s5_v40 s5_j s5_v39 s5_v38 s5_p s5_v37 s5_v36 s5_v35
    s5_v34 s4_v33 s4_v32 s4_pi s4_v31 s4_v30 s4_v29 s4_v28
    s4_v27 s4_v26 s4_v25 s3_a2 s3_v24 s3_v23 s3_v22 s3_v21
    s3_v20 s3_v19 s2_v18 s2_a1 s2_v17 s2_v16 s2_v15 s2_v14
    s1_v6 s1_v7 s1_v8 s1_v9 cget cset].
  repeat split;
    repeat first [one_map | rewrite H1 | rewrite H2 | rewrite H3 |
      rewrite H4 | rewrite H5 | rewrite H41 | rewrite H42 | rewrite H46 |
      rewrite H47 | rewrite H59 | rewrite H60 | rewrite SHIFTRANGE | scalar];
    try reflexivity; try assumption.
  all: vm_compute; reflexivity.
Qed.

Lemma production_loop_atoms_chunks :
  production_loop_atoms =
    stage1_atoms ++ stage2_atoms ++ stage3_atoms ++ stage4_atoms ++
    stage5_atoms ++ stage6_atoms ++ stage7_atoms.
Proof. vm_compute. reflexivity. Qed.

Lemma stage7_rel_is_mob_step : forall b t q st,
  stage7_rel b t q st ->
  stage0_rel b (Int64.add t (cI 1)) (production_mob_step t q) st.
Proof.
  intros b t [a pos neg pi p j] st REL.
  cbn [stage7_rel core_rel stage0_rel production_mob_step
    production_mob_step_fields] in *.
  unfold s7_neg, s7_pos, s7_v58, s7_v57, s7_v56, s7_v55, s7_v54,
    s7_v53, s7_v52, s7_v51, s7_v50, s7_v49, s7_v48, s6_v47,
    s6_v46, s6_v45, s5_v44, s5_v43, s5_v42, s5_v41, s5_v40,
    s5_j, s5_v39, s5_v38, s5_p, s5_v37, s5_v36, s5_v35, s5_v34,
    s4_v33, s4_v32, s4_pi, s4_v31, s4_v30, s4_v29, s4_v28,
    s4_v27, s4_v26, s4_v25, s3_a2, s3_v24, s3_v23, s3_v22,
    s3_v21, s3_v20, s3_v19, s2_v18, s2_a1, s2_v17, s2_v16,
    s2_v15, s2_v14, s1_v9, s1_v8, s1_v7, s1_v10, s1_v6 in *.
  exact REL.
Qed.

Theorem production_loop_atoms_refine_step : forall b t q st,
  stage0_rel b t q st -> production_mob_step_safe t q = true ->
  exists st',
    run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      production_loop_atoms st = Some st' /\
    stage0_rel b (Int64.add t (cI 1)) (production_mob_step t q) st'.
Proof.
  intros b t [a pos neg pi p j] st REL SAFE.
  change
    (cindex_ok (s1_v8 t j) && cindex_ok (s1_v9 t j) &&
     negb (Int64.eq (s3_v19 p) (cI 0)) &&
     cindex_ok (s4_v32 t pi j) && cindex_ok (s5_v42 t) &&
     cindex_ok (s5_v43 t) = true) in SAFE.
  repeat rewrite Bool.andb_true_iff in SAFE.
  destruct SAFE as [[[[[SAFE8 SAFE9] NZ] SAFE32] SAFE42] SAFE43].
  change (cindex_ok (s1_v8 t j) = true) in SAFE8.
  change (cindex_ok (s1_v9 t j) = true) in SAFE9.
  change (negb (Int64.eq (s3_v19 p) (cI 0)) = true) in NZ.
  change (cindex_ok (s4_v32 t pi j) = true) in SAFE32.
  change (cindex_ok (s5_v42 t) = true) in SAFE42.
  change (cindex_ok (s5_v43 t) = true) in SAFE43.
  destruct (stage1_forward b t
    {| mob_cells := a; mob_pos := pos; mob_neg := neg; mob_pi := pi;
       mob_p := p; mob_j := j |} st REL SAFE8) as [st1 [RUN1 R1]].
  destruct (stage2_forward b t _ st1 R1 SAFE8 SAFE9) as [st2 [RUN2 R2]].
  destruct (stage3_forward b t _ st2 R2 SAFE9 NZ) as [st3 [RUN3 R3]].
  destruct (stage4_forward b t _ st3 R3 SAFE32) as [st4 [RUN4 R4]].
  destruct (stage5_forward b t _ st4 R4 SAFE42) as [st5 [RUN5 R5]].
  destruct (stage6_forward b t _ st5 R5 SAFE43) as [st6 [RUN6 R6]].
  destruct (stage7_forward b t _ st6 R6) as [st7 [RUN7 R7]].
  exists st7. split.
  - rewrite production_loop_atoms_chunks.
    rewrite run_flat_atoms_app, RUN1.
    rewrite run_flat_atoms_app, RUN2.
    rewrite run_flat_atoms_app, RUN3.
    rewrite run_flat_atoms_app, RUN4.
    rewrite run_flat_atoms_app, RUN5.
    rewrite run_flat_atoms_app, RUN6.
    exact RUN7.
  - now apply stage7_rel_is_mob_step.
Qed.

(** A binary runner which threads the loop counter explicitly.  Unlike a
    Peano iteration certificate, its proof term has logarithmic recursion
    depth and can be shared at every [Qed] boundary. *)
Fixpoint checked_run_mob_pos_t (n : positive) (start : int64) (q : mob_state)
    : option (int64 * mob_state) :=
  match n with
  | xH =>
      if Int64.ltu start (cI 302298) && production_mob_step_safe start q
      then Some (Int64.add start (cI 1), production_mob_step start q)
      else None
  | xO half =>
      match checked_run_mob_pos_t half start q with
      | Some (mid_t, mid_q) => checked_run_mob_pos_t half mid_t mid_q
      | None => None
      end
  | xI half =>
      match checked_run_mob_pos_t half start q with
      | Some (mid_t, mid_q) =>
          match checked_run_mob_pos_t half mid_t mid_q with
          | Some (last_t, last_q) =>
              if Int64.ltu last_t (cI 302298) &&
                   production_mob_step_safe last_t last_q
              then Some (Int64.add last_t (cI 1),
                          production_mob_step last_t last_q)
              else None
          | None => None
          end
      | None => None
      end
  end.

Fixpoint run_loop_atoms_pos (n : positive) (b : block) (st : flat_state)
    : option flat_state :=
  match n with
  | xH => run_flat_atoms (genv_cenv (globalenv prog)) b
      production_array_bytes production_loop_atoms st
  | xO half =>
      match run_loop_atoms_pos half b st with
      | Some mid => run_loop_atoms_pos half b mid
      | None => None
      end
  | xI half =>
      match run_loop_atoms_pos half b st with
      | Some mid =>
          match run_loop_atoms_pos half b mid with
          | Some last => run_flat_atoms (genv_cenv (globalenv prog)) b
              production_array_bytes production_loop_atoms last
          | None => None
          end
      | None => None
      end
  end.

Theorem checked_run_mob_pos_t_refines_flat : forall n b start q st end_t final,
  stage0_rel b start q st ->
  checked_run_mob_pos_t n start q = Some (end_t, final) ->
  exists st',
    run_loop_atoms_pos n b st = Some st' /\
    stage0_rel b end_t final st'.
Proof.
  induction n as [half IH|half IH|]; intros b start q st end_t final REL CHECK.
  - cbn [checked_run_mob_pos_t] in CHECK.
    destruct (checked_run_mob_pos_t half start q)
      as [[mid_t mid_q]|] eqn:CHECK1; try discriminate.
    destruct (checked_run_mob_pos_t half mid_t mid_q)
      as [[last_t last_q]|] eqn:CHECK2; try discriminate.
    destruct (Int64.ltu last_t (cI 302298) &&
      production_mob_step_safe last_t last_q) eqn:LAST; try discriminate.
    inversion CHECK; subst end_t final.
    apply andb_prop in LAST as [_ SAFE].
    destruct (IH b start q st mid_t mid_q REL CHECK1)
      as [mid [RUN1 REL1]].
    destruct (IH b mid_t mid_q mid last_t last_q REL1 CHECK2)
      as [last [RUN2 REL2]].
    destruct (production_loop_atoms_refine_step b last_t last_q last REL2 SAFE)
      as [st' [RUN3 REL3]].
    exists st'. split; [cbn [run_loop_atoms_pos]; rewrite RUN1, RUN2; exact RUN3|].
    exact REL3.
  - cbn [checked_run_mob_pos_t] in CHECK.
    destruct (checked_run_mob_pos_t half start q)
      as [[mid_t mid_q]|] eqn:CHECK1; try discriminate.
    destruct (IH b start q st mid_t mid_q REL CHECK1)
      as [mid [RUN1 REL1]].
    destruct (IH b mid_t mid_q mid end_t final REL1 CHECK)
      as [st' [RUN2 REL2]].
    exists st'. split; [cbn [run_loop_atoms_pos]; rewrite RUN1; exact RUN2|].
    exact REL2.
  - cbn [checked_run_mob_pos_t] in CHECK.
    destruct (Int64.ltu start (cI 302298) &&
      production_mob_step_safe start q) eqn:STEP; try discriminate.
    inversion CHECK; subst end_t final.
    apply andb_prop in STEP as [_ SAFE].
    destruct (production_loop_atoms_refine_step b start q st REL SAFE)
      as [st' [RUN REL']].
    exists st'. split; assumption.
Qed.

Definition production_mob_t_final : int64 * mob_state :=
  (cI 302298, production_mob_final).

Theorem production_candidate_all_steps_safe_t :
  checked_run_mob_pos_t 302298%positive (cI 0) production_mob_initial =
    Some production_mob_t_final.
Proof. vm_compute. reflexivity. Qed.

Theorem production_all_iterations_refine_flat : forall b st,
  stage0_rel b (cI 0) production_mob_initial st ->
  exists st',
    run_loop_atoms_pos 302298%positive b st = Some st' /\
    stage0_rel b (cI 302298) production_mob_final st'.
Proof.
  intros b st REL.
  eapply checked_run_mob_pos_t_refines_flat.
  - exact REL.
  - exact production_candidate_all_steps_safe_t.
Qed.

Definition production_loop_guard : statement :=
  match production_loop_head with
  | Ssequence guard _ => guard
  | _ => Sskip
  end.
Definition production_loop_incr : statement :=
  match production_loop_parts with
  | Some (_, _, incr, _) => incr
  | None => Sskip
  end.
Definition production_loop_head_atoms : list statement :=
  Eval vm_compute in flatten_sequence production_loop_head.
Definition production_loop_guard_atoms : list statement :=
  Eval vm_compute in flatten_sequence production_loop_guard.
Definition production_loop_guard_exact : statement :=
  Eval vm_compute in production_loop_guard.

Lemma production_loop_head_atoms_decompose :
  production_loop_head_atoms = production_loop_guard_atoms ++ production_loop_atoms.
Proof. vm_compute. reflexivity. Qed.

Lemma production_loop_incr_is_skip : production_loop_incr = Sskip.
Proof. vm_compute. reflexivity. Qed.

Theorem production_loop_guard_forward : forall b t q st,
  stage0_rel b t q st ->
  Int64.ltu t (cI 302298) = true ->
  run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
    production_loop_guard_atoms st = Some st.
Proof.
  intros b t [a pos neg pi p j] [le cells] REL GUARD.
  cbn [stage0_rel flat_array flat_temps] in REL.
  destruct REL as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  cbn [production_loop_guard_atoms run_flat_atoms].
  fold _v_59 in *.
  unfold run_flat_atom.
  cbn [run_flat_fuel eval_flat].
  rewrite H59.
  scalar.
  change (Int64.ltu t (cI 302298) = true) in GUARD.
  lazymatch goal with
  | |- context [Int64.ltu t ?limit] =>
      assert (GUARD' : Int64.ltu t limit = true) by
        (replace limit with (cI 302298) by (vm_compute; reflexivity);
         exact GUARD)
  end.
  rewrite GUARD'. cbn. reflexivity.
Qed.

Theorem production_loop_head_refine_step : forall b t q st,
  stage0_rel b t q st ->
  Int64.ltu t (cI 302298) = true ->
  production_mob_step_safe t q = true ->
  exists st',
    run_flat_atoms (genv_cenv (globalenv prog)) b production_array_bytes
      production_loop_head_atoms st = Some st' /\
    stage0_rel b (Int64.add t (cI 1)) (production_mob_step t q) st'.
Proof.
  intros b t q st REL GUARD SAFE.
  pose proof (production_loop_guard_forward b t q st REL GUARD) as RUNGUARD.
  destruct (production_loop_atoms_refine_step b t q st REL SAFE)
    as [st' [RUNWORK REL']].
  exists st'. split; [|exact REL'].
  rewrite production_loop_head_atoms_decompose, run_flat_atoms_app, RUNGUARD.
  exact RUNWORK.
Qed.


Inductive production_iteration
    (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
    (ge : genv) (en : env)
    : temp_env -> mem -> temp_env -> mem -> Prop :=
| production_iteration_intro : forall le m le1 m1 le2 m2,
    ClightBigstep.exec_stmt fe ge en le m production_loop_head E0
      le1 m1 Out_normal ->
    ClightBigstep.exec_stmt fe ge en le1 m1 production_loop_incr E0
      le2 m2 Out_normal ->
    production_iteration fe ge en le m le2 m2.

Fixpoint production_iterations_pos (n : positive)
    (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
    (ge : genv) (en : env)
    (le : temp_env) (m : mem) (le' : temp_env) (m' : mem) : Prop :=
  match n with
  | xH => production_iteration fe ge en le m le' m'
  | xO half =>
      exists le_mid m_mid,
        production_iterations_pos half fe ge en le m le_mid m_mid /\
        production_iterations_pos half fe ge en le_mid m_mid le' m'
  | xI half =>
      exists le_mid m_mid le_last m_last,
        production_iterations_pos half fe ge en le m le_mid m_mid /\
        production_iterations_pos half fe ge en le_mid m_mid le_last m_last /\
        production_iteration fe ge en le_last m_last le' m'
  end.

Lemma production_iterations_prepend_loop : forall n fe ge en le m le' m' le2 m2 out,
  production_iterations_pos n fe ge en le m le' m' ->
  ClightBigstep.exec_stmt fe ge en le' m'
    (Sloop production_loop_head production_loop_incr) E0 le2 m2 out ->
  ClightBigstep.exec_stmt fe ge en le m
    (Sloop production_loop_head production_loop_incr) E0 le2 m2 out.
Proof.
  induction n as [half IH|half IH|]; intros fe ge en le m le' m' le2 m2 out RUNS TAIL.
  - cbn in RUNS.
    destruct RUNS as [le_mid [m_mid [le_last [m_last [FIRST [SECOND LAST]]]]]].
    destruct LAST as [le0 m0 le1 m1 le3 m3 HEAD INCR].
    assert (TAILLAST : ClightBigstep.exec_stmt fe ge en le0 m0
      (Sloop production_loop_head production_loop_incr) E0 le2 m2 out).
    { replace E0 with (E0 ** E0 ** E0) by reflexivity.
      eapply exec_Sloop_loop; eauto; constructor. }
    apply (IH fe ge en le_mid m_mid le0 m0 le2 m2 out SECOND) in TAILLAST.
    now apply (IH fe ge en le m le_mid m_mid le2 m2 out FIRST) in TAILLAST.
  - cbn in RUNS.
    destruct RUNS as [le_mid [m_mid [FIRST SECOND]]].
    apply (IH fe ge en le_mid m_mid le' m' le2 m2 out SECOND) in TAIL.
    now apply (IH fe ge en le m le_mid m_mid le2 m2 out FIRST).
  - cbn in RUNS.
    destruct RUNS as [le0 m0 le1 m1 le3 m3 HEAD INCR].
    replace E0 with (E0 ** E0 ** E0) by reflexivity.
    eapply exec_Sloop_loop; eauto; constructor.
Qed.


Theorem production_one_iteration_sem : forall fe en b t q flat m,
  stage0_rel b t q flat ->
  Int64.ltu t (cI 302298) = true ->
  production_mob_step_safe t q = true ->
  flat_block_rel flat.(flat_array) m b production_array_bytes ->
  exists flat' m',
    stage0_rel b (Int64.add t (cI 1)) (production_mob_step t q) flat' /\
    flat_block_rel flat'.(flat_array) m' b production_array_bytes /\
    production_iteration fe (globalenv prog) en
      flat.(flat_temps) m flat'.(flat_temps) m'.
Proof.
  intros fe en b t q flat m REL GUARD SAFE MEMREL.
  destruct (production_loop_head_refine_step b t q flat REL GUARD SAFE)
    as [flat' [RUN REL']].
  change (run_flat_atoms (genv_cenv (globalenv prog)) b
    production_array_bytes (flatten_sequence production_loop_head) flat =
    Some flat') in RUN.
  destruct (run_flatten_sequence_sim fe (globalenv prog) en
    (genv_cenv (globalenv prog)) b production_array_bytes
    production_loop_head flat m flat' eq_refl
    ltac:(vm_compute; reflexivity) MEMREL RUN)
    as [m' [HEAD MEMREL']].
  exists flat', m'. split; [exact REL'|]. split; [exact MEMREL'|].
  econstructor; [exact HEAD|].
  rewrite production_loop_incr_is_skip. constructor.
Qed.

Theorem checked_run_mob_pos_t_refines_semantics :
  forall n fe en b start q flat m end_t final,
  stage0_rel b start q flat ->
  flat_block_rel flat.(flat_array) m b production_array_bytes ->
  checked_run_mob_pos_t n start q = Some (end_t, final) ->
  exists flat' m',
    stage0_rel b end_t final flat' /\
    flat_block_rel flat'.(flat_array) m' b production_array_bytes /\
    production_iterations_pos n fe (globalenv prog) en
      flat.(flat_temps) m flat'.(flat_temps) m'.
Proof.
  induction n as [half IH|half IH|];
    intros fe en b start q flat m end_t final REL MEMREL CHECK.
  - cbn [checked_run_mob_pos_t] in CHECK.
    destruct (checked_run_mob_pos_t half start q)
      as [[mid_t mid_q]|] eqn:CHECK1; try discriminate.
    destruct (checked_run_mob_pos_t half mid_t mid_q)
      as [[last_t last_q]|] eqn:CHECK2; try discriminate.
    destruct (Int64.ltu last_t (cI 302298) &&
      production_mob_step_safe last_t last_q) eqn:LAST; try discriminate.
    inversion CHECK; subst end_t final.
    apply andb_prop in LAST as [GUARD SAFE].
    destruct (IH fe en b start q flat m mid_t mid_q REL MEMREL CHECK1)
      as [mid [m_mid [REL1 [MEM1 ITER1]]]].
    destruct (IH fe en b mid_t mid_q mid m_mid last_t last_q
      REL1 MEM1 CHECK2) as [last [m_last [REL2 [MEM2 ITER2]]]].
    destruct (production_one_iteration_sem fe en b last_t last_q last m_last
      REL2 GUARD SAFE MEM2) as [flat' [m' [REL3 [MEM3 ITER3]]]].
    exists flat', m'. split; [exact REL3|]. split; [exact MEM3|].
    cbn. exists (flat_temps mid), m_mid, (flat_temps last), m_last.
    repeat split; assumption.
  - cbn [checked_run_mob_pos_t] in CHECK.
    destruct (checked_run_mob_pos_t half start q)
      as [[mid_t mid_q]|] eqn:CHECK1; try discriminate.
    destruct (IH fe en b start q flat m mid_t mid_q REL MEMREL CHECK1)
      as [mid [m_mid [REL1 [MEM1 ITER1]]]].
    destruct (IH fe en b mid_t mid_q mid m_mid end_t final
      REL1 MEM1 CHECK) as [flat' [m' [REL2 [MEM2 ITER2]]]].
    exists flat', m'. split; [exact REL2|]. split; [exact MEM2|].
    cbn. exists (flat_temps mid), m_mid. split; assumption.
  - cbn [checked_run_mob_pos_t] in CHECK.
    destruct (Int64.ltu start (cI 302298) &&
      production_mob_step_safe start q) eqn:STEP; try discriminate.
    inversion CHECK; subst end_t final.
    apply andb_prop in STEP as [GUARD SAFE].
    destruct (production_one_iteration_sem fe en b start q flat m
      REL GUARD SAFE MEMREL) as [flat' [m' [REL' [MEM' ITER]]]].
    exists flat', m'. split; [exact REL'|]. split; assumption.
Qed.

Theorem production_all_iterations_semantics : forall fe en b flat m,
  stage0_rel b (cI 0) production_mob_initial flat ->
  flat_block_rel flat.(flat_array) m b production_array_bytes ->
  exists flat' m',
    stage0_rel b (cI 302298) production_mob_final flat' /\
    flat_block_rel flat'.(flat_array) m' b production_array_bytes /\
    production_iterations_pos 302298%positive fe (globalenv prog) en
      flat.(flat_temps) m flat'.(flat_temps) m'.
Proof.
  intros fe en b flat m REL MEMREL.
  eapply checked_run_mob_pos_t_refines_semantics with
    (end_t := cI 302298) (final := production_mob_final).
  - exact REL.
  - exact MEMREL.
  - change (checked_run_mob_pos_t 302298%positive (cI 0)
      production_mob_initial = Some production_mob_t_final).
    exact production_candidate_all_steps_safe_t.
Qed.


Lemma production_loop_head_structure :
  production_loop_head = Ssequence production_loop_guard production_loop_work.
Proof. vm_compute. reflexivity. Qed.

Lemma production_guard_false_flat : forall b q flat,
  stage0_rel b (cI 302298) q flat ->
  run_flat_fuel 3 (genv_cenv (globalenv prog)) b production_array_bytes
    production_loop_guard flat = Some (flat, Out_break).
Proof.
  intros b [a pos neg pi p j] [le cells] REL.
  cbn [stage0_rel flat_array flat_temps] in REL.
  destruct REL as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  change (run_flat_fuel 3 (genv_cenv (globalenv prog)) b
    production_array_bytes production_loop_guard_exact
      {| flat_temps := le; flat_array := cells |} =
    Some ({| flat_temps := le; flat_array := cells |}, Out_break)).
  unfold production_loop_guard_exact.
  cbn [run_flat_fuel eval_flat].
  unfold _v_59 in H59.
  rewrite H59. scalar.
  vm_compute. reflexivity.
Qed.

Theorem production_final_head_break : forall fe en b q flat m,
  stage0_rel b (cI 302298) q flat ->
  flat_block_rel flat.(flat_array) m b production_array_bytes ->
  exists m',
    ClightBigstep.exec_stmt fe (globalenv prog) en flat.(flat_temps) m
      production_loop_head E0 flat.(flat_temps) m' Out_break /\
    flat_block_rel flat.(flat_array) m' b production_array_bytes.
Proof.
  intros fe en b q flat m REL MEMREL.
  pose proof (production_guard_false_flat b q flat REL) as RUN.
  destruct (run_flat_fuel_sim 3 (genv_cenv (globalenv prog)) b
    production_array_bytes production_loop_guard flat m flat Out_break
    ltac:(vm_compute; reflexivity) MEMREL RUN) as [m' [MEMRUN MEMREL']].
  exists m'. split; [|exact MEMREL'].
  rewrite production_loop_head_structure.
  eapply exec_Sseq_2.
  - eapply ClightMemorySem.run_mem_fuel_sound. exact MEMRUN.
  - discriminate.
Qed.

Theorem production_loop_semantics : forall fe en b flat m,
  stage0_rel b (cI 0) production_mob_initial flat ->
  flat_block_rel flat.(flat_array) m b production_array_bytes ->
  exists flat' m',
    stage0_rel b (cI 302298) production_mob_final flat' /\
    flat_block_rel flat'.(flat_array) m' b production_array_bytes /\
    ClightBigstep.exec_stmt fe (globalenv prog) en flat.(flat_temps) m
      (Sloop production_loop_head production_loop_incr) E0
      flat'.(flat_temps) m' Out_normal.
Proof.
  intros fe en b flat m REL MEMREL.
  destruct (production_all_iterations_semantics fe en b flat m REL MEMREL)
    as [flat' [m' [REL' [MEMREL' ITERS]]]].
  destruct (production_final_head_break fe en b production_mob_final
    flat' m' REL' MEMREL') as [m_final [BREAK MEMFINAL]].
  assert (TAIL : ClightBigstep.exec_stmt fe (globalenv prog) en
    flat'.(flat_temps) m'
    (Sloop production_loop_head production_loop_incr) E0
    flat'.(flat_temps) m_final Out_normal).
  { eapply exec_Sloop_stop1; [exact BREAK|constructor]. }
  exists flat', m_final. split; [exact REL'|]. split; [exact MEMFINAL|].
  eapply production_iterations_prepend_loop; eauto.
Qed.


Inductive production_exec_list
    (fe : genv -> function -> list val -> mem -> env -> temp_env -> mem -> Prop)
    (ge : genv) (en : env)
    : temp_env -> mem -> list statement -> temp_env -> mem -> outcome -> Prop :=
| production_exec_list_nil : forall le m,
    production_exec_list fe ge en le m nil le m Out_normal
| production_exec_list_cons : forall le m s rest le1 m1 le2 m2 out,
    ClightBigstep.exec_stmt fe ge en le m s E0 le1 m1 Out_normal ->
    production_exec_list fe ge en le1 m1 rest le2 m2 out ->
    production_exec_list fe ge en le m (s :: rest) le2 m2 out
| production_exec_list_stop : forall le m s rest le1 m1 out,
    ClightBigstep.exec_stmt fe ge en le m s E0 le1 m1 out ->
    out <> Out_normal ->
    production_exec_list fe ge en le m (s :: rest) le1 m1 out.

Lemma production_exec_list_app_normal : forall fe ge en xs ys le m le1 m1 le2 m2 out,
  production_exec_list fe ge en le m xs le1 m1 Out_normal ->
  production_exec_list fe ge en le1 m1 ys le2 m2 out ->
  production_exec_list fe ge en le m (xs ++ ys) le2 m2 out.
Proof.
  intros fe ge en xs.
  induction xs as [|x rest IH];
    intros ys le m le1 m1 le2 m2 out FIRST SECOND.
  - cbn. inversion FIRST; subst; exact SECOND.
  - cbn. inversion FIRST; subst.
    + econstructor; [eassumption|].
      eapply IH; eauto.
    + exfalso.
      match goal with
      | HNE : Out_normal <> Out_normal |- _ => exact (HNE eq_refl)
      end.
Qed.

Lemma production_exec_list_app_inv : forall fe ge en xs ys le m le' m' out,
  production_exec_list fe ge en le m (xs ++ ys) le' m' out ->
  (exists le_mid m_mid,
      production_exec_list fe ge en le m xs le_mid m_mid Out_normal /\
      production_exec_list fe ge en le_mid m_mid ys le' m' out) \/
  (production_exec_list fe ge en le m xs le' m' out /\ out <> Out_normal).
Proof.
  intros fe ge en xs.
  induction xs as [|x rest IH]; intros ys le m le' m' out RUN.
  - left. exists le, m. split; [constructor|exact RUN].
  - cbn in RUN. inversion RUN; subst.
    + match goal with
      | TAIL : production_exec_list fe ge en _ _ (rest ++ ys) _ _ _ |- _ =>
        destruct (IH ys _ _ _ _ _ TAIL)
          as [[le_mid [m_mid [LEFT RIGHT]]]|[STOP NON]]
      end.
      * left. exists le_mid, m_mid. split; [econstructor; eauto|exact RIGHT].
      * right. split; [econstructor; eauto|exact NON].
    + right. split; [eapply production_exec_list_stop; eauto|assumption].
Qed.

Lemma production_exec_list_singleton : forall fe ge en s le m le' m' out,
  production_exec_list fe ge en le m (s :: nil) le' m' out ->
  ClightBigstep.exec_stmt fe ge en le m s E0 le' m' out.
Proof.
  intros fe ge en s le m le' m' out RUN.
  inversion RUN; subst.
  - match goal with
    | TAIL : production_exec_list fe ge en _ _ nil _ _ _ |- _ =>
        inversion TAIL; subst; assumption
    end.
  - assumption.
Qed.

Theorem production_exec_flat_sequence : forall fe ge en s le m le' m' out,
  production_exec_list fe ge en le m (flat_sequence s) le' m' out ->
  ClightBigstep.exec_stmt fe ge en le m s E0 le' m' out.
Proof.
  intros fe ge en s.
  induction s; intros le m le' m' out RUN;
    try (apply production_exec_list_singleton; exact RUN).
  cbn [flat_sequence] in RUN.
  destruct (production_exec_list_app_inv fe ge en
    (flat_sequence s1) (flat_sequence s2) le m le' m' out RUN)
    as [[le_mid [m_mid [RUN1 RUN2]]]|[RUN1 NON]].
  - replace E0 with (E0 ** E0) by reflexivity.
    eapply exec_Sseq_1.
    + eapply IHs1; exact RUN1.
    + eapply IHs2; exact RUN2.
  - eapply exec_Sseq_2.
    + eapply IHs1; exact RUN1.
    + exact NON.
Qed.


Theorem production_run_flat_list_sim : forall fuel fe ge en ce b limit xs flat m flat' out,
  ce = genv_cenv ge ->
  Forall (fun s => flat_stmt_supported s = true) xs ->
  flat_block_rel flat.(flat_array) m b limit ->
  run_flat_list fuel ce b limit xs flat = Some (flat', out) ->
  exists m',
    production_exec_list fe ge en flat.(flat_temps) m xs
      flat'.(flat_temps) m' out /\
    flat_block_rel flat'.(flat_array) m' b limit.
Proof.
  intros fuel fe ge en ce b limit xs.
  induction xs as [|x rest IH]; intros flat m flat' out CE SAFE REL RUN.
  - cbn [run_flat_list] in RUN. inversion RUN; subst.
    exists m. split; [constructor|exact REL].
  - inversion SAFE as [|? ? SAFEX SAFEREST].
    cbn [run_flat_list] in RUN.
    destruct (run_flat_fuel fuel ce b limit x flat)
      as [[mid headout]|] eqn:HEADRUN; try discriminate.
    destruct (run_flat_fuel_sim fuel ce b limit x flat m mid headout
      SAFEX REL HEADRUN) as [m1 [MEMRUN REL1]].
    assert (EXECHEAD : ClightBigstep.exec_stmt fe ge en flat.(flat_temps) m
      x E0 mid.(flat_temps) m1 headout).
    { subst ce. eapply ClightMemorySem.run_mem_fuel_sound. exact MEMRUN. }
    destruct headout.
    + inversion RUN; subst. exists m1. split.
      * eapply production_exec_list_stop; [exact EXECHEAD|discriminate].
      * exact REL1.
    + inversion RUN; subst. exists m1. split.
      * eapply production_exec_list_stop; [exact EXECHEAD|discriminate].
      * exact REL1.
    + destruct (IH mid m1 flat' out CE SAFEREST REL1 RUN)
        as [m' [EXECREST REL']].
      exists m'. split; [econstructor; eauto|exact REL'].
    + inversion RUN; subst. exists m1. split.
      * eapply production_exec_list_stop; [exact EXECHEAD|discriminate].
      * exact REL1.
Qed.


Definition production_prefix : list statement :=
  match production_loop_parts with
  | Some (prefix, _, _, _) => prefix
  | None => nil
  end.
Definition production_suffix : list statement :=
  match production_loop_parts with
  | Some (_, _, _, suffix) => suffix
  | None => nil
  end.
Definition production_before_loop : flat_state :=
  Eval vm_compute in
  match run_flat_list 3 (genv_cenv (globalenv prog)) production_array_block
      production_array_bytes production_prefix production_flat_initial with
  | Some (st, Out_normal) => st
  | _ => production_flat_initial
  end.

Lemma production_prefix_supported_bool :
  forallb flat_stmt_supported production_prefix = true.
Proof. vm_compute. reflexivity. Qed.
Lemma production_prefix_supported :
  Forall (fun s => flat_stmt_supported s = true) production_prefix.
Proof.
  apply Forall_forall. apply List.forallb_forall.
  exact production_prefix_supported_bool.
Qed.

Lemma production_suffix_supported_bool :
  forallb flat_stmt_supported production_suffix = true.
Proof. vm_compute. reflexivity. Qed.
Lemma production_suffix_supported :
  Forall (fun s => flat_stmt_supported s = true) production_suffix.
Proof.
  apply Forall_forall. apply List.forallb_forall.
  exact production_suffix_supported_bool.
Qed.

Lemma production_prefix_run :
  run_flat_list 3 (genv_cenv (globalenv prog)) production_array_block
    production_array_bytes production_prefix production_flat_initial =
  Some (production_before_loop, Out_normal).
Proof. vm_compute. reflexivity. Qed.

Lemma production_before_loop_rel :
  stage0_rel production_array_block (cI 0) production_mob_initial
    production_before_loop.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma production_final_return_value :
  Int64.sub
    (Int64.add production_mob_final.(mob_pos) (cI 100001))
    production_mob_final.(mob_neg) = cI 99952.
Proof. vm_compute. reflexivity. Qed.

Opaque production_mob_final.

Definition production_suffix_exact : list statement :=
  Eval vm_compute in production_suffix.

Theorem production_suffix_forward : forall b flat,
  stage0_rel b (cI 302298) production_mob_final flat ->
  exists flat',
    run_flat_list 3 (genv_cenv (globalenv prog)) b production_array_bytes
      production_suffix flat =
    Some (flat', Out_return (Some (Vlong (cI 99952), tulong))).
Proof.
  intros b [le cells] REL.
  cbn [stage0_rel] in REL.
  destruct REL as [HA [H1 [H2 [H3 [H4 [H5 [H59 H60]]]]]]].
  cbn [flat_temps flat_array] in HA, H1, H2, H3, H4, H5, H59, H60.
  change (exists flat',
    run_flat_list 3 (genv_cenv (globalenv prog)) b
      production_array_bytes production_suffix_exact
      {| flat_temps := le; flat_array := cells |} =
    Some (flat', Out_return (Some (Vlong (cI 99952), tulong)))).
  unfold production_suffix_exact.
  cbn [run_flat_list run_flat_fuel eval_flat].
  fold _v_1 _v_2 _v_10 _v_11 in *.
  scalar. rewrite H1. scalar.
  repeat progress (one_map; scalar).
  rewrite H2. scalar.
  repeat progress (one_map; scalar).
  lazymatch goal with
  | |- context [Int64.sub
      (Int64.add (mob_pos production_mob_final) ?literal)
      (mob_neg production_mob_final)] =>
      let term := constr:(Int64.sub
        (Int64.add (mob_pos production_mob_final) literal)
        (mob_neg production_mob_final)) in
      assert (RETURNVALUE : term = cI 99952) by
        (change (Int64.sub
          (Int64.add (mob_pos production_mob_final) (cI 100001))
          (mob_neg production_mob_final) = cI 99952);
         exact production_final_return_value);
      rewrite RETURNVALUE
  end.
  eexists. reflexivity.
Qed.

Lemma production_initial_memory_exists_exact :
  exists m, Genv.init_mem prog = Some m.
Proof.
  apply Genv.init_mem_exists.
  intros id v IN.
  vm_compute in IN.
  do 56 (destruct IN as [IN|IN]; [discriminate|]).
  destruct IN as [IN|IN].
  - inversion IN; subst. split.
    + vm_compute. repeat constructor. exists 0%Z. reflexivity.
    + intros i o ADDR. vm_compute in ADDR.
      destruct ADDR as [ADDR|ADDR]; [discriminate|contradiction].
  - destruct IN as [IN|IN]; [discriminate|contradiction].
Qed.

Lemma production_body_flat_parts :
  flat_sequence (fn_body production_f) =
    production_prefix ++
      (Sloop production_loop_head production_loop_incr) :: production_suffix.
Proof. vm_compute. reflexivity. Qed.

Lemma production_cells_exact :
  Genv.find_symbol (Genv.globalenv prog) _cells =
      Some production_array_block /\
  Genv.find_var_info (Genv.globalenv prog) production_array_block =
      Some v_cells.
Proof. vm_compute. split; reflexivity. Qed.

Theorem production_body_exec_99952 : forall m,
  Genv.init_mem prog = Some m ->
  exists le' m',
    ClightBigstep.exec_stmt function_entry2 (globalenv prog) empty_env
      (production_le0 production_arg) m (fn_body production_f) E0 le' m'
      (Out_return (Some (Vlong (cI 99952), tulong))).
Proof.
  intros m INIT.
  destruct production_cells_exact as [_ FIND].
  assert (MEM0 : flat_block_rel production_flat_initial.(flat_array) m
      production_array_block production_array_bytes).
  { cbn [production_flat_initial flat_array].
    eapply production_zero_global_rel; eauto. }
  destruct (production_run_flat_list_sim 3 function_entry2
    (globalenv prog) empty_env (genv_cenv (globalenv prog))
    production_array_block production_array_bytes production_prefix
    production_flat_initial m production_before_loop Out_normal
    eq_refl production_prefix_supported MEM0 production_prefix_run)
    as [m_pre [PREFIX MEMPRE]].
  destruct (production_loop_semantics function_entry2 empty_env
    production_array_block production_before_loop m_pre
    production_before_loop_rel MEMPRE)
    as [flat_loop [m_loop [RELLOOP [MEMLOOP LOOP]]]].
  destruct (production_suffix_forward production_array_block flat_loop RELLOOP)
    as [flat_after RUNSUFFIX].
  destruct (production_run_flat_list_sim 3 function_entry2
    (globalenv prog) empty_env (genv_cenv (globalenv prog))
    production_array_block production_array_bytes production_suffix
    flat_loop m_loop flat_after
    (Out_return (Some (Vlong (cI 99952), tulong)))
    eq_refl production_suffix_supported MEMLOOP RUNSUFFIX)
    as [m_after [SUFFIX MEMAFTER]].
  assert (MID : production_exec_list function_entry2 (globalenv prog)
    empty_env production_before_loop.(flat_temps) m_pre
    ((Sloop production_loop_head production_loop_incr) :: production_suffix)
    flat_after.(flat_temps) m_after
    (Out_return (Some (Vlong (cI 99952), tulong)))).
  { econstructor; [exact LOOP|exact SUFFIX]. }
  exists flat_after.(flat_temps), m_after.
  apply production_exec_flat_sequence.
  rewrite production_body_flat_parts.
  eapply production_exec_list_app_normal; [exact PREFIX|exact MID].
Qed.

Theorem production_funcall_99952 : forall m,
  Genv.init_mem prog = Some m ->
  exists m',
    ClightBigstep.eval_funcall function_entry2 (globalenv prog) m
      (Internal production_f) (production_arg :: nil) E0 m'
      (Vlong (cI 99952)).
Proof.
  intros m INIT.
  destruct (production_body_exec_99952 m INIT) as [le' [m' BODY]].
  exists m'.
  eapply eval_funcall_internal with
    (e := empty_env) (le1 := production_le0 production_arg)
    (le2 := le') (m1 := m) (m2 := m')
    (out := Out_return (Some (Vlong (cI 99952), tulong))).
  - constructor.
    + rewrite production_vars_nil. constructor.
    + exact production_params_norepet.
    + exact production_params_temps_disjoint.
    + rewrite production_vars_nil. constructor.
    + exact (production_bind_one production_arg).
  - exact BODY.
  - vm_compute. split; congruence.
  - reflexivity.
Qed.

Theorem production_end_to_end_99952 :
  exists m m',
    Genv.init_mem prog = Some m /\
    ClightBigstep.eval_funcall function_entry2 (globalenv prog) m
      (Internal production_f) (production_arg :: nil) E0 m'
      (Vlong (cI 99952)).
Proof.
  destruct production_initial_memory_exists_exact as [m INIT].
  destruct (production_funcall_99952 m INIT) as [m' CALL].
  exists m, m'. split; assumption.
Qed.

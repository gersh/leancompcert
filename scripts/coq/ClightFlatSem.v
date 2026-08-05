(* ClightFlatSem.v

   A fast executable shadow semantics for the pointer-backed Clight fragment.
   Array cells are indexed by byte offset in a PTree; a missing entry denotes
   the all-zero initial value.  The evaluator deliberately follows
   ClightMemorySem.run_mem_fuel's control-flow structure, but does not build or
   reduce CompCert memory values.  Its simulation into CompCert memory is
   proved below the executable definitions.
 *)

From compcert Require Import Coqlib Maps Integers Values Events Memory.
From compcert Require Import Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
From Direct Require Import ClightMemorySem.

Definition flat_cells : Type := PTree.t int64.

(** [offset + 1] makes byte offset zero a valid positive PTree key.  All
    callers establish nonnegative offsets before using the map. *)
Definition flat_key (offset: Z) : positive := Z.to_pos (offset + 1).

Definition flat_load (cells: flat_cells) (offset: Z) : int64 :=
  match PTree.get (flat_key offset) cells with
  | Some value => value
  | None => Int64.zero
  end.

Definition flat_store (cells: flat_cells) (offset: Z) (value: int64)
    : flat_cells :=
  PTree.set (flat_key offset) value cells.

Definition flat_offset_ok (limit offset: Z) : bool :=
  (0 <=? offset) && (offset + 8 <=? limit) && (offset mod 8 =? 0).

Definition same_block (b1 b2: block) : bool :=
  if peq b1 b2 then true else false.

Definition flat_numeric_type (ty: type) : bool :=
  match typeconv ty with
  | Tint _ _ _ | Tlong _ _ | Tfloat _ _ => true
  | _ => false
  end.

Definition flat_value_matches (v: val) (ty: type) : bool :=
  match v, typeconv ty with
  | Vundef, _ => true
  | Vint _, Tint _ _ _ => true
  | Vlong _, Tlong _ _ => true
  | Vfloat _, Tfloat F64 _ => true
  | Vsingle _, Tfloat F32 _ => true
  | Vptr _ _, Tpointer _ _ => true
  | _, _ => false
  end.

Definition flat_checked (ty: type) (candidate: option val) : option val :=
  match candidate with
  | Some v => if flat_value_matches v ty then Some v else None
  | None => None
  end.

Definition flat_add_types (t1 t2: type) : bool :=
  match typeconv t1, typeconv t2 with
  | Tpointer _ _, Tlong _ _ | Tlong _ _, Tpointer _ _ => true
  | Tpointer _ _, Tint _ _ _ | Tint _ _ _, Tpointer _ _ => true
  | a, b => flat_numeric_type a && flat_numeric_type b
  end.

Definition flat_binary_types (op: binary_operation) (t1 t2: type) : bool :=
  match op with
  | Oadd => flat_add_types t1 t2
  | _ => flat_numeric_type t1 && flat_numeric_type t2
  end.

Fixpoint flat_expr_supported (a: expr) : bool :=
  match a with
  | Econst_int _ _ | Econst_long _ _ | Etempvar _ _ => true
  | Ederef addr ty =>
      flat_expr_supported addr &&
      match access_mode ty with By_value Mint64 => true | _ => false end
  | Ebinop op a1 a2 _ =>
      flat_expr_supported a1 && flat_expr_supported a2 &&
      flat_binary_types op (typeof a1) (typeof a2)
  | Ecast a1 ty =>
      flat_expr_supported a1 && flat_numeric_type (typeof a1) &&
      flat_numeric_type ty
  | _ => false
  end.

Fixpoint flat_stmt_supported (s: statement) : bool :=
  match s with
  | Sskip | Sbreak | Scontinue => true
  | Sassign (Ederef addr ty) rhs =>
      flat_expr_supported addr && flat_expr_supported rhs &&
      flat_numeric_type (typeof rhs) && flat_numeric_type ty &&
      match access_mode ty with By_value Mint64 => true | _ => false end
  | Sassign _ _ => false
  | Sset _ a => flat_expr_supported a
  | Ssequence s1 s2 => flat_stmt_supported s1 && flat_stmt_supported s2
  | Sifthenelse a s1 s2 =>
      flat_expr_supported a && flat_numeric_type (typeof a) &&
      flat_stmt_supported s1 && flat_stmt_supported s2
  | Sloop s1 s2 => flat_stmt_supported s1 && flat_stmt_supported s2
  | Sreturn None => true
  | Sreturn (Some a) => flat_expr_supported a
  | _ => false
  end.

Lemma sem_cast_flat_numeric : forall v t1 t2 m1 m2,
  flat_value_matches v t1 = true ->
  flat_numeric_type t1 = true -> flat_numeric_type t2 = true ->
  sem_cast v t1 t2 m1 = sem_cast v t1 t2 m2.
Proof.
  intros v t1 t2 m1 m2 HV H1 H2.
  unfold flat_numeric_type in H1, H2.
  unfold flat_value_matches in HV.
  unfold sem_cast, classify_cast.
  destruct t1; destruct t2;
    repeat match goal with
    | x : intsize |- _ => destruct x
    | x : floatsize |- _ => destruct x
    end; simpl in *; try discriminate;
    destruct v; simpl in *; try discriminate; try reflexivity;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?; simpl
    end; reflexivity.
Qed.

Lemma bool_val_flat_numeric : forall v ty m1 m2,
  flat_value_matches v ty = true ->
  flat_numeric_type ty = true ->
  bool_val v ty m1 = bool_val v ty m2.
Proof.
  intros v ty m1 m2 HV H.
  unfold flat_value_matches in HV.
  unfold flat_numeric_type in H. unfold bool_val, classify_bool.
  destruct ty;
    repeat match goal with
    | x : intsize |- _ => destruct x
    | x : floatsize |- _ => destruct x
    end; simpl in *; try discriminate; destruct v; simpl in *;
    try discriminate;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?; simpl
    end; reflexivity.
Qed.

Lemma sem_binary_flat_types : forall ce op v1 t1 v2 t2 m1 m2,
  flat_value_matches v1 t1 = true ->
  flat_value_matches v2 t2 = true ->
  flat_binary_types op t1 t2 = true ->
  sem_binary_operation ce op v1 t1 v2 t2 m1 =
    sem_binary_operation ce op v1 t1 v2 t2 m2.
Proof.
  intros ce op v1 t1 v2 t2 m1 m2 HV1 HV2 H.
  unfold flat_value_matches in HV1, HV2.
  destruct op; unfold flat_binary_types in H; simpl in H;
    unfold sem_binary_operation;
    destruct t1; destruct t2;
    repeat match goal with
    | x : intsize |- _ => destruct x
    | x : floatsize |- _ => destruct x
    end; simpl in *; try discriminate;
    destruct v1; destruct v2; simpl in *; try discriminate;
    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b eqn:?; simpl
    end; try reflexivity.
Qed.

(** Expressions are evaluated with [Mem.empty] for scalar and pointer
    arithmetic.  In the accepted fragment those operations do not inspect
    memory; dereferences are handled explicitly through [flat_cells]. *)
Fixpoint eval_flat (ce: composite_env) (array_block: block) (limit: Z)
    (cells: flat_cells) (le: temp_env) (a: expr) : option val :=
  match a with
  | Econst_int i ty => flat_checked ty (Some (Vint i))
  | Econst_long i ty => flat_checked ty (Some (Vlong i))
  | Etempvar id ty => flat_checked ty (PTree.get id le)
  | Ederef addr ty =>
      match eval_flat ce array_block limit cells le addr with
      | Some (Vptr b ofs) =>
          let offset := Ptrofs.unsigned ofs in
          if same_block b array_block && flat_offset_ok limit offset then
            match access_mode ty with
            | By_value Mint64 =>
                flat_checked ty (Some (Vlong (flat_load cells offset)))
            | _ => None
            end
          else None
      | _ => None
      end
  | Ebinop op a1 a2 ty =>
      match eval_flat ce array_block limit cells le a1,
            eval_flat ce array_block limit cells le a2 with
      | Some v1, Some v2 =>
          flat_checked ty
            (sem_binary_operation ce op v1 (typeof a1) v2 (typeof a2) Mem.empty)
      | _, _ => None
      end
  | Ecast a1 ty =>
      match eval_flat ce array_block limit cells le a1 with
      | Some v1 => flat_checked ty (sem_cast v1 (typeof a1) ty Mem.empty)
      | None => None
      end
  | _ => None
  end.

Lemma flat_checked_matches : forall ty candidate v,
  flat_checked ty candidate = Some v -> flat_value_matches v ty = true.
Proof.
  intros ty candidate v H. unfold flat_checked in H.
  destruct candidate as [candidate|]; try discriminate.
  destruct (flat_value_matches candidate ty) eqn:MATCH; try discriminate.
  inversion H; subst; exact MATCH.
Qed.

Lemma flat_checked_some_inv : forall ty candidate v,
  flat_checked ty candidate = Some v -> candidate = Some v.
Proof.
  intros ty candidate v H. unfold flat_checked in H.
  destruct candidate as [candidate|]; try discriminate.
  destruct (flat_value_matches candidate ty); try discriminate.
  now inversion H.
Qed.

Lemma eval_flat_matches : forall ce b limit cells le a v,
  eval_flat ce b limit cells le a = Some v ->
  flat_value_matches v (typeof a) = true.
Proof.
  intros ce b limit cells le a.
  destruct a; simpl; intros v H; try discriminate;
    try (eapply flat_checked_matches; exact H);
    repeat match goal with
    | h : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
    | h : context [if ?x then _ else _] |- _ => destruct x eqn:?
    end; try discriminate; try (eapply flat_checked_matches; exact H).
  all: inversion H; subst.
  all: match goal with
  | h : flat_value_matches _ _ = true |- _ => exact h
  | h : typeconv ?ty = ?converted |- _ =>
      unfold flat_value_matches; rewrite h; reflexivity
  end.
Qed.

Record flat_state : Type := {
  flat_temps : temp_env;
  flat_array : flat_cells
}.

Definition flat_result : Type := flat_state * outcome.

Fixpoint run_flat_fuel (fuel: nat) (ce: composite_env)
    (array_block: block) (limit: Z) (s: statement) (st: flat_state)
    : option flat_result :=
  match fuel with
  | O => None
  | S fuel' =>
      match s with
      | Sskip => Some (st, Out_normal)
      | Sassign (Ederef addr ty) rhs =>
          match eval_flat ce array_block limit st.(flat_array)
                  st.(flat_temps) addr with
          | Some (Vptr b ofs) =>
              let offset := Ptrofs.unsigned ofs in
              if same_block b array_block && flat_offset_ok limit offset then
                match eval_flat ce array_block limit st.(flat_array)
                        st.(flat_temps) rhs with
                | Some v2 =>
                    match sem_cast v2 (typeof rhs) ty Mem.empty,
                          access_mode ty with
                    | Some (Vlong value), By_value Mint64 =>
                        Some
                          ({| flat_temps := st.(flat_temps);
                              flat_array := flat_store st.(flat_array)
                                offset value |}, Out_normal)
                    | _, _ => None
                    end
                | None => None
                end
              else None
          | _ => None
          end
      | Sassign _ _ => None
      | Sset id a =>
          match eval_flat ce array_block limit st.(flat_array)
                  st.(flat_temps) a with
          | Some v =>
              Some ({| flat_temps := PTree.set id v st.(flat_temps);
                       flat_array := st.(flat_array) |}, Out_normal)
          | None => None
          end
      | Ssequence s1 s2 =>
          match run_flat_fuel fuel' ce array_block limit s1 st with
          | Some (st1, Out_normal) =>
              run_flat_fuel fuel' ce array_block limit s2 st1
          | res => res
          end
      | Sifthenelse a s1 s2 =>
          match eval_flat ce array_block limit st.(flat_array)
                  st.(flat_temps) a with
          | Some v =>
              match bool_val v (typeof a) Mem.empty with
              | Some b => run_flat_fuel fuel' ce array_block limit
                  (if b then s1 else s2) st
              | None => None
              end
          | None => None
          end
      | Sloop s1 s2 =>
          match run_flat_fuel fuel' ce array_block limit s1 st with
          | Some (st1, Out_break) => Some (st1, Out_normal)
          | Some (st1, Out_return ret) => Some (st1, Out_return ret)
          | Some (st1, Out_normal)
          | Some (st1, Out_continue) =>
              match run_flat_fuel fuel' ce array_block limit s2 st1 with
              | Some (st2, Out_break) => Some (st2, Out_normal)
              | Some (st2, Out_return ret) => Some (st2, Out_return ret)
              | Some (st2, Out_normal) =>
                  run_flat_fuel fuel' ce array_block limit (Sloop s1 s2) st2
              | Some (_, Out_continue) => None
              | None => None
              end
          | None => None
          end
      | Sbreak => Some (st, Out_break)
      | Scontinue => Some (st, Out_continue)
      | Sreturn None => Some (st, Out_return None)
      | Sreturn (Some a) =>
          match eval_flat ce array_block limit st.(flat_array)
                  st.(flat_temps) a with
          | Some v => Some (st, Out_return (Some (v, typeof a)))
          | None => None
          end
      | _ => None
      end
  end.

(* ------------------------------------------------------------------ *)
(* Binary-fuel execution helpers. *)

(** Flatten only sequence nodes.  This is used to isolate a generated
    function's unique top-level loop without changing any atomic statement. *)
Fixpoint flat_sequence (s: statement) : list statement :=
  match s with
  | Ssequence s1 s2 => flat_sequence s1 ++ flat_sequence s2
  | _ => s :: nil
  end.

Fixpoint split_first_loop_list (prefix_rev: list statement)
    (statements: list statement)
    : option (list statement * statement * statement * list statement) :=
  match statements with
  | nil => None
  | Sloop s1 s2 :: suffix =>
      Some (List.rev prefix_rev, s1, s2, suffix)
  | stmt :: rest => split_first_loop_list (stmt :: prefix_rev) rest
  end.

Definition split_first_loop (s: statement)
    : option (list statement * statement * statement * list statement) :=
  split_first_loop_list nil (flat_sequence s).

(** Execute a flattened sequence with a small per-statement fuel bound. *)
Fixpoint run_flat_list (fuel: nat) (ce: composite_env)
    (array_block: block) (limit: Z) (statements: list statement)
    (st: flat_state) : option flat_result :=
  match statements with
  | nil => Some (st, Out_normal)
  | stmt :: rest =>
      match run_flat_fuel fuel ce array_block limit stmt st with
      | Some (next, Out_normal) =>
          run_flat_list fuel ce array_block limit rest next
      | result => result
      end
  end.

Definition run_flat_normal (fuel: nat) (ce: composite_env)
    (array_block: block) (limit: Z) (stmt: statement) (st: flat_state)
    : option flat_state :=
  match run_flat_fuel fuel ce array_block limit stmt st with
  | Some (next, Out_normal) => Some next
  | _ => None
  end.

(** Repeat a statement [positive] times.  Recursing over the binary
    representation keeps proof reduction depth logarithmic in the production
    loop count. *)
Fixpoint repeat_flat_pos (count: positive) (fuel: nat) (ce: composite_env)
    (array_block: block) (limit: Z) (stmt: statement) (st: flat_state)
    : option flat_state :=
  match count with
  | xH => run_flat_normal fuel ce array_block limit stmt st
  | xO half =>
      match repeat_flat_pos half fuel ce array_block limit stmt st with
      | Some mid => repeat_flat_pos half fuel ce array_block limit stmt mid
      | None => None
      end
  | xI half =>
      match repeat_flat_pos half fuel ce array_block limit stmt st with
      | Some mid =>
          match repeat_flat_pos half fuel ce array_block limit stmt mid with
          | Some almost => run_flat_normal fuel ce array_block limit stmt almost
          | None => None
          end
      | None => None
      end
  end.

(** Execute a generated single-loop function by splitting its top-level
    sequence, repeating the loop iteration with binary fuel, then running the
    loop once more to check its terminating guard and finally the suffix. *)
Definition run_flat_rolled (count: positive) (fuel: nat) (ce: composite_env)
    (array_block: block) (limit: Z) (body: statement) (st: flat_state)
    : option flat_result :=
  match split_first_loop body with
  | Some (prefix, loop_body, loop_incr, suffix) =>
      match run_flat_list fuel ce array_block limit prefix st with
      | Some (before_loop, Out_normal) =>
          let iteration := Ssequence loop_body loop_incr in
          match repeat_flat_pos count fuel ce array_block limit iteration
                  before_loop with
          | Some after_iterations =>
              match run_flat_fuel fuel ce array_block limit
                      (Sloop loop_body loop_incr) after_iterations with
              | Some (after_loop, Out_normal) =>
                  run_flat_list fuel ce array_block limit suffix after_loop
              | _ => None
              end
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

(** A flat array is represented by one valid CompCert block. *)
Definition flat_block_rel (cells: flat_cells) (m: mem) (b: block)
    (limit: Z) : Prop :=
  forall offset,
    0 <= offset -> offset + 8 <= limit -> offset mod 8 = 0 ->
    Mem.valid_access m Mint64 b offset Writable /\
    Mem.load Mint64 m b offset = Some (Vlong (flat_load cells offset)).

Lemma flat_key_nonnegative_inj : forall x y,
  0 <= x -> 0 <= y -> flat_key x = flat_key y -> x = y.
Proof.
  unfold flat_key. intros x y HX HY EQ.
  apply (f_equal Z.pos) in EQ. simpl in EQ.
  repeat rewrite Z2Pos.id in EQ by lia. lia.
Qed.

Lemma flat_load_store_same : forall cells offset value,
  0 <= offset ->
  flat_load (flat_store cells offset value) offset = value.
Proof.
  intros. unfold flat_load, flat_store.
  now rewrite PTree.gss.
Qed.

Lemma flat_load_store_other : forall cells written read value,
  0 <= written -> 0 <= read -> read <> written ->
  flat_load (flat_store cells written value) read = flat_load cells read.
Proof.
  intros cells written read value HW HR HNE.
  unfold flat_load, flat_store.
  rewrite PTree.gso; auto.
  intro EQ. apply HNE. symmetry.
  now apply flat_key_nonnegative_inj.
Qed.

(** The fundamental store step for the shadow-memory simulation. *)
Theorem flat_block_rel_store :
  forall cells m b limit offset value m',
  flat_block_rel cells m b limit ->
  0 <= offset -> offset + 8 <= limit -> offset mod 8 = 0 ->
  Mem.store Mint64 m b offset (Vlong value) = Some m' ->
  flat_block_rel (flat_store cells offset value) m' b limit.
Proof.
  intros cells m b limit offset value m' REL HOFF HEND HALIGN STORE.
  intros read HREAD HREADEND HREADALIGN.
  split.
  - eapply Mem.store_valid_access_1; eauto. apply REL; auto.
  - destruct (Z.eq_dec read offset) as [SAME|DIFF].
    + subst read. rewrite flat_load_store_same by auto.
    pose proof (Mem.load_store_same Mint64 m b offset (Vlong value) m' STORE)
      as LOAD. cbn in LOAD. exact LOAD.
    + rewrite flat_load_store_other by auto.
    rewrite (Mem.load_store_other Mint64 m b offset (Vlong value) m' STORE
      Mint64 b read).
    * exact (proj2 (REL read HREAD HREADEND HREADALIGN)).
    * right. simpl.
      assert (HREADMULT : read = 8 * (read / 8)).
      { pose proof (Z.div_mod read 8 ltac:(lia)). lia. }
      assert (HOFFMULT : offset = 8 * (offset / 8)).
      { pose proof (Z.div_mod offset 8 ltac:(lia)). lia. }
      destruct (Z_lt_ge_dec read offset).
      -- left. nia.
      -- right. nia.
Qed.

Lemma eval_flat_sim : forall ce array_block limit cells le m a v,
  flat_expr_supported a = true ->
  flat_block_rel cells m array_block limit ->
  eval_flat ce array_block limit cells le a = Some v ->
  eval_mem ce m le a = Some v.
Proof.
  intros ce array_block limit cells le m a.
  induction a; simpl; intros v SAFE REL RUN; try discriminate.
  - repeat match type of RUN with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    | context [if ?x then _ else _] => destruct x eqn:?
    end; try discriminate; exact RUN.
  - repeat match type of RUN with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    | context [if ?x then _ else _] => destruct x eqn:?
    end; try discriminate; exact RUN.
  - destruct (PTree.get i le) as [temp|] eqn:TEMP; try discriminate.
    apply flat_checked_some_inv in RUN. inversion RUN; reflexivity.
  - apply andb_true_iff in SAFE as [SAFEADDR ACCESS].
    destruct (eval_flat ce array_block limit cells le a) as [address|]
      eqn:EADDR; try discriminate.
    destruct address; try discriminate.
    destruct (same_block b array_block &&
      flat_offset_ok limit (Ptrofs.unsigned i)) eqn:BOUNDS;
      try discriminate.
    apply andb_true_iff in BOUNDS as [BLOCK OFFSET].
    unfold same_block in BLOCK. destruct (peq b array_block); try discriminate.
    subst b.
    unfold flat_offset_ok in OFFSET.
    repeat rewrite andb_true_iff in OFFSET.
    destruct OFFSET as [[HOFF HEND] HALIGN].
    apply Z.leb_le in HOFF. apply Z.leb_le in HEND.
    apply Z.eqb_eq in HALIGN.
    destruct (access_mode t) eqn:MODE; try discriminate.
    destruct m0; try discriminate.
    repeat match type of RUN with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    | context [if ?x then _ else _] => destruct x eqn:?
    end; try discriminate.
    inversion RUN; subst v.
    rewrite (IHa (Vptr array_block i) SAFEADDR REL eq_refl).
    simpl.
    exact (proj2 (REL (Ptrofs.unsigned i) HOFF HEND HALIGN)).
  - repeat rewrite andb_true_iff in SAFE.
    destruct SAFE as [[SAFE1 SAFE2] TYPES].
    destruct (eval_flat ce array_block limit cells le a1) as [v1|]
      eqn:E1; try discriminate.
    destruct (eval_flat ce array_block limit cells le a2) as [v2|]
      eqn:E2; try discriminate.
    apply flat_checked_some_inv in RUN.
    rewrite (IHa1 v1 SAFE1 REL eq_refl), (IHa2 v2 SAFE2 REL eq_refl).
    rewrite <- (sem_binary_flat_types ce b v1 (typeof a1) v2 (typeof a2)
      Mem.empty m (eval_flat_matches _ _ _ _ _ _ _ E1)
      (eval_flat_matches _ _ _ _ _ _ _ E2) TYPES).
    exact RUN.
  - repeat rewrite andb_true_iff in SAFE.
    destruct SAFE as [[SAFEEXPR SOURCE] TARGET].
    destruct (eval_flat ce array_block limit cells le a) as [v1|]
      eqn:E1; try discriminate.
    apply flat_checked_some_inv in RUN.
    rewrite (IHa v1 SAFEEXPR REL eq_refl).
    rewrite <- (sem_cast_flat_numeric v1 (typeof a) t Mem.empty m
      (eval_flat_matches _ _ _ _ _ _ _ E1) SOURCE TARGET).
    exact RUN.
Qed.

(** Successful shadow execution can be replayed in CompCert memory while
    preserving the block relation. *)
Theorem run_flat_fuel_sim :
  forall fuel ce array_block limit s flat m flat' out,
  flat_stmt_supported s = true ->
  flat_block_rel flat.(flat_array) m array_block limit ->
  run_flat_fuel fuel ce array_block limit s flat = Some (flat', out) ->
  exists m',
    run_mem_fuel fuel ce m s flat.(flat_temps) =
      Some (flat'.(flat_temps), (m', out)) /\
    flat_block_rel flat'.(flat_array) m' array_block limit.
Proof.
  induction fuel as [|fuel IH]; intros ce array_block limit s flat m flat' out
    SAFE REL RUN; try discriminate.
  destruct s; simpl in SAFE, RUN; try discriminate.
  - inversion RUN; subst. exists m. split; auto.
  - destruct e; try discriminate.
    repeat rewrite andb_true_iff in SAFE.
    destruct SAFE as [[[[SAFEADDR SAFERHS] RHSTYPE] TARGETTYPE] ACCESS].
    destruct (eval_flat ce array_block limit (flat_array flat)
      (flat_temps flat) e) as [address|] eqn:EADDR; try discriminate.
    destruct address; try discriminate.
    destruct (same_block b array_block &&
      flat_offset_ok limit (Ptrofs.unsigned i)) eqn:BOUNDS; try discriminate.
    apply andb_true_iff in BOUNDS as [BLOCK OFFSET].
    unfold same_block in BLOCK. destruct (peq b array_block); try discriminate.
    subst b.
    unfold flat_offset_ok in OFFSET.
    repeat rewrite andb_true_iff in OFFSET.
    destruct OFFSET as [[HOFF HEND] HALIGN].
    apply Z.leb_le in HOFF. apply Z.leb_le in HEND.
    apply Z.eqb_eq in HALIGN.
    destruct (eval_flat ce array_block limit (flat_array flat)
      (flat_temps flat) e0) as [rhs|] eqn:ERHS; try discriminate.
    destruct (sem_cast rhs (typeof e0) t Mem.empty) as [casted|]
      eqn:CAST; try discriminate.
    destruct casted; try discriminate.
    destruct (access_mode t) eqn:MODE; try discriminate.
    destruct m0; try discriminate.
    inversion RUN; subst flat' out.
    assert (ACTUAL_ADDR : eval_mem ce m (flat_temps flat) e =
        Some (Vptr array_block i)).
    { eapply eval_flat_sim; eauto. }
    assert (ACTUAL_RHS : eval_mem ce m (flat_temps flat) e0 = Some rhs).
    { eapply eval_flat_sim; eauto. }
    assert (CAST_ACTUAL : sem_cast rhs (typeof e0) t m = Some (Vlong i0)).
    { rewrite <- (sem_cast_flat_numeric rhs (typeof e0) t Mem.empty m
        (eval_flat_matches _ _ _ _ _ _ _ ERHS) RHSTYPE TARGETTYPE).
      exact CAST. }
    destruct (Mem.valid_access_store m Mint64 array_block
      (Ptrofs.unsigned i) (Vlong i0)) as [m' STORE].
    { exact (proj1 (REL (Ptrofs.unsigned i) HOFF HEND HALIGN)). }
    exists m'. split.
    + simpl. rewrite ACTUAL_ADDR, ACTUAL_RHS, CAST_ACTUAL, MODE. simpl.
      rewrite STORE. reflexivity.
    + eapply flat_block_rel_store; eauto.
  - destruct (eval_flat ce array_block limit (flat_array flat)
      (flat_temps flat) e) as [value|] eqn:EVAL; try discriminate.
    inversion RUN; subst flat' out.
    exists m. split.
    + simpl. rewrite (eval_flat_sim ce array_block limit (flat_array flat)
        (flat_temps flat) m e value SAFE REL EVAL). reflexivity.
    + exact REL.
  - apply andb_true_iff in SAFE as [SAFE1 SAFE2].
    destruct (run_flat_fuel fuel ce array_block limit s1 flat)
      as [[mid outcome1]|] eqn:RUN1; try discriminate.
    destruct (IH ce array_block limit s1 flat m mid outcome1 SAFE1 REL RUN1)
      as [m1 [ACTUAL1 REL1]].
    destruct outcome1.
    + inversion RUN; subst. exists m1. split; [simpl; rewrite ACTUAL1|]; auto.
    + inversion RUN; subst. exists m1. split; [simpl; rewrite ACTUAL1|]; auto.
    + destruct (run_flat_fuel fuel ce array_block limit s2 mid)
        as [[finish outcome2]|] eqn:RUN2; try discriminate.
      destruct (IH ce array_block limit s2 mid m1 finish outcome2 SAFE2 REL1 RUN2)
        as [m2 [ACTUAL2 REL2]].
      inversion RUN; subst. exists m2. split.
      * simpl. rewrite ACTUAL1. exact ACTUAL2.
      * exact REL2.
    + inversion RUN; subst. exists m1. split; [simpl; rewrite ACTUAL1|]; auto.
  - repeat rewrite andb_true_iff in SAFE.
    destruct SAFE as [[[SAFEEXPR EXPRTYPE] SAFE1] SAFE2].
    destruct (eval_flat ce array_block limit (flat_array flat)
      (flat_temps flat) e) as [value|] eqn:EVAL; try discriminate.
    destruct (bool_val value (typeof e) Mem.empty) as [choice|]
      eqn:BOOL; try discriminate.
    assert (EVAL_ACTUAL : eval_mem ce m (flat_temps flat) e = Some value).
    { eapply eval_flat_sim; eauto. }
    assert (BOOL_ACTUAL : bool_val value (typeof e) m = Some choice).
    { rewrite <- (bool_val_flat_numeric value (typeof e) Mem.empty m
        (eval_flat_matches _ _ _ _ _ _ _ EVAL) EXPRTYPE). exact BOOL. }
    destruct choice.
    + destruct (IH ce array_block limit s1 flat m flat' out SAFE1 REL RUN)
        as [m' [ACTUAL REL']].
      exists m'. split; [simpl; rewrite EVAL_ACTUAL, BOOL_ACTUAL|]; auto.
    + destruct (IH ce array_block limit s2 flat m flat' out SAFE2 REL RUN)
        as [m' [ACTUAL REL']].
      exists m'. split; [simpl; rewrite EVAL_ACTUAL, BOOL_ACTUAL|]; auto.
  - apply andb_true_iff in SAFE as [SAFE1 SAFE2].
    assert (SAFELOOP : flat_stmt_supported (Sloop s1 s2) = true).
    { simpl. rewrite SAFE1, SAFE2. reflexivity. }
    destruct (run_flat_fuel fuel ce array_block limit s1 flat)
      as [[mid outcome1]|] eqn:RUN1; try discriminate.
    destruct (IH ce array_block limit s1 flat m mid outcome1 SAFE1 REL RUN1)
      as [m1 [ACTUAL1 REL1]].
    destruct outcome1.
    + inversion RUN; subst. exists m1. split; [simpl; rewrite ACTUAL1|]; auto.
    + destruct (run_flat_fuel fuel ce array_block limit s2 mid)
        as [[after_incr outcome2]|] eqn:RUN2; try discriminate.
      destruct (IH ce array_block limit s2 mid m1 after_incr outcome2
        SAFE2 REL1 RUN2) as [m2 [ACTUAL2 REL2]].
      destruct outcome2; try discriminate.
      * inversion RUN; subst. exists m2. split.
        -- simpl. rewrite ACTUAL1, ACTUAL2. reflexivity.
        -- exact REL2.
      * destruct (IH ce array_block limit (Sloop s1 s2) after_incr m2
          flat' out SAFELOOP REL2 RUN) as [m' [ACTUAL3 REL3]].
        exists m'. split.
        -- simpl. rewrite ACTUAL1, ACTUAL2. exact ACTUAL3.
        -- exact REL3.
      * inversion RUN; subst. exists m2. split.
        -- simpl. rewrite ACTUAL1, ACTUAL2. reflexivity.
        -- exact REL2.
    + destruct (run_flat_fuel fuel ce array_block limit s2 mid)
        as [[after_incr outcome2]|] eqn:RUN2; try discriminate.
      destruct (IH ce array_block limit s2 mid m1 after_incr outcome2
        SAFE2 REL1 RUN2) as [m2 [ACTUAL2 REL2]].
      destruct outcome2; try discriminate.
      * inversion RUN; subst. exists m2. split.
        -- simpl. rewrite ACTUAL1, ACTUAL2. reflexivity.
        -- exact REL2.
      * destruct (IH ce array_block limit (Sloop s1 s2) after_incr m2
          flat' out SAFELOOP REL2 RUN) as [m' [ACTUAL3 REL3]].
        exists m'. split.
        -- simpl. rewrite ACTUAL1, ACTUAL2. exact ACTUAL3.
        -- exact REL3.
      * inversion RUN; subst. exists m2. split.
        -- simpl. rewrite ACTUAL1, ACTUAL2. reflexivity.
        -- exact REL2.
    + inversion RUN; subst. exists m1. split; [simpl; rewrite ACTUAL1|]; auto.
  - inversion RUN; subst. exists m. split; auto.
  - inversion RUN; subst. exists m. split; auto.
  - destruct o as [ret|].
    + destruct (eval_flat ce array_block limit (flat_array flat)
        (flat_temps flat) ret) as [value|] eqn:EVAL; try discriminate.
      assert (EVAL_ACTUAL : eval_mem ce m (flat_temps flat) ret = Some value).
      { eapply eval_flat_sim; eauto. }
      inversion RUN; subst. exists m. split.
      * simpl. rewrite EVAL_ACTUAL. reflexivity.
      * exact REL.
    + inversion RUN; subst. exists m. split; auto.
Qed.

(** Small computation rules used by artifact refinements.  Stating these as
    lemmas keeps large generated straight-line bodies from unfolding all of
    [Cop] merely to reduce a scalar operation. *)
Lemma flat_checked_long : forall x,
  flat_checked tulong (Some (Vlong x)) = Some (Vlong x).
Proof. reflexivity. Qed.

Lemma flat_checked_int : forall x,
  flat_checked tint (Some (Vint x)) = Some (Vint x).
Proof. reflexivity. Qed.

Lemma flat_checked_uchar : forall x,
  flat_checked tuchar (Some (Vint x)) = Some (Vint x).
Proof. reflexivity. Qed.

Lemma flat_checked_bool_int : forall b,
  flat_checked tint (Some (Val.of_bool b)) = Some (Val.of_bool b).
Proof. destruct b; reflexivity. Qed.

Lemma flat_checked_bool_uchar : forall b,
  flat_checked tuchar (Some (Val.of_bool b)) = Some (Val.of_bool b).
Proof. destruct b; reflexivity. Qed.

Lemma flat_checked_ptr_u64 : forall b ofs,
  flat_checked (tptr tulong) (Some (Vptr b ofs)) = Some (Vptr b ofs).
Proof. reflexivity. Qed.

Lemma sem_mul_u64 : forall ce x y,
  sem_binary_operation ce Omul (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Vlong (Int64.mul x y)).
Proof. reflexivity. Qed.

Lemma sem_add_u64 : forall ce x y,
  sem_binary_operation ce Oadd (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Vlong (Int64.add x y)).
Proof. reflexivity. Qed.

Lemma sem_sub_u64 : forall ce x y,
  sem_binary_operation ce Osub (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Vlong (Int64.sub x y)).
Proof. reflexivity. Qed.

Lemma sem_lt_u64 : forall ce x y,
  sem_binary_operation ce Olt (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Val.of_bool (Int64.ltu x y)).
Proof. reflexivity. Qed.

Lemma sem_gt_u64 : forall ce x y,
  sem_binary_operation ce Ogt (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Val.of_bool (Int64.ltu y x)).
Proof. reflexivity. Qed.

Lemma sem_eq_u64 : forall ce x y,
  sem_binary_operation ce Oeq (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Val.of_bool (Int64.eq x y)).
Proof. reflexivity. Qed.

Lemma sem_ne_u64 : forall ce x y,
  sem_binary_operation ce One (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Val.of_bool (negb (Int64.eq x y))).
Proof. reflexivity. Qed.

Lemma sem_mod_u64 : forall ce x y,
  Int64.eq y Int64.zero = false ->
  sem_binary_operation ce Omod (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Vlong (Int64.modu x y)).
Proof.
  intros ce x y NZ.
  change ((if Int64.eq y Int64.zero then None
    else Some (Vlong (Int64.modu x y))) = Some (Vlong (Int64.modu x y))).
  now rewrite NZ.
Qed.

Lemma sem_xor_u64 : forall ce x y,
  sem_binary_operation ce Oxor (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Vlong (Int64.xor x y)).
Proof. reflexivity. Qed.

Lemma sem_or_u64 : forall ce x y,
  sem_binary_operation ce Oor (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Vlong (Int64.or x y)).
Proof. reflexivity. Qed.

Lemma sem_and_u64 : forall ce x y,
  sem_binary_operation ce Oand (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Vlong (Int64.and x y)).
Proof. reflexivity. Qed.

Lemma sem_shr_u64 : forall ce x y,
  Int64.ltu y (Int64.repr 64) = true ->
  sem_binary_operation ce Oshr (Vlong x) tulong (Vlong y) tulong Mem.empty =
  Some (Vlong (Int64.shru x y)).
Proof.
  intros ce x y RANGE.
  change ((if Int64.ltu y (Int64.repr 64)
    then Some (Vlong (Int64.shru x y)) else None) =
    Some (Vlong (Int64.shru x y))).
  now rewrite RANGE.
Qed.

Lemma cast_bool_uchar : forall b,
  sem_cast (Val.of_bool b) tint tuchar Mem.empty = Some (Val.of_bool b).
Proof. destruct b; reflexivity. Qed.

Lemma cast_bool_u64 : forall b,
  sem_cast (Val.of_bool b) tuchar tulong Mem.empty =
  Some (Vlong (if b then Int64.one else Int64.zero)).
Proof. destruct b; reflexivity. Qed.

Lemma cast_u64_u64 : forall x,
  sem_cast (Vlong x) tulong tulong Mem.empty = Some (Vlong x).
Proof. reflexivity. Qed.

Lemma sem_add_ptr_u64 : forall ce b x,
  sem_binary_operation ce Oadd (Vptr b Ptrofs.zero) (tptr tulong)
    (Vlong x) tulong Mem.empty =
  Some (Vptr b (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 x))).
Proof.
  intros ce b x. unfold sem_binary_operation, sem_add.
  change (Some (Vptr b
    (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 x)))) =
    Some (Vptr b
      (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 x)))).
  now rewrite Ptrofs.add_zero_l.
Qed.

Lemma same_block_refl : forall b, same_block b b = true.
Proof. intros b. unfold same_block. destruct (peq b b); congruence. Qed.

(** A mutable [Init_space] global establishes the zero-default shadow-array
    relation directly from CompCert's initialization characterization. *)
Theorem init_space_flat_block_rel :
  forall (F V: Type) (p: AST.program F V) b gv m limit,
  Genv.find_var_info (Genv.globalenv p) b = Some gv ->
  Genv.init_mem p = Some m ->
  gvar_init gv = Init_space limit :: nil ->
  gvar_volatile gv = false ->
  gvar_readonly gv = false ->
  flat_block_rel (PTree.empty int64) m b limit.
Proof.
  intros F V p b gv m limit FIND INIT CONTENTS NOTVOL MUTABLE.
  intros offset HOFF HEND HALIGN.
  pose proof (@Genv.init_mem_characterization F V p b gv m FIND INIT)
    as CHARACTERIZATION.
  destruct CHARACTERIZATION as [RANGE [_ [INITIALIZED _]]].
  specialize (INITIALIZED NOTVOL).
  rewrite CONTENTS in INITIALIZED. simpl in INITIALIZED.
  destruct INITIALIZED as [ZERO _].
  assert (LIMITNONNEG : 0 <= limit) by lia.
  split.
  - unfold Mem.valid_access. split.
    + unfold Mem.range_perm. intros address HAT.
      rewrite CONTENTS in RANGE. simpl in RANGE.
      rewrite Z.max_l in RANGE by exact LIMITNONNEG.
      unfold Genv.perm_globvar in RANGE.
      rewrite NOTVOL, MUTABLE in RANGE.
      simpl in RANGE, HAT. apply RANGE. lia.
    + simpl. apply Z.mod_divide; lia.
  - specialize (ZERO Mint64 offset HOFF HEND).
    assert (ALIGN : (align_chunk Mint64 | offset)).
    { simpl. apply Z.mod_divide; lia. }
    specialize (ZERO ALIGN). simpl in ZERO.
    unfold flat_load. rewrite PTree.gempty. exact ZERO.
Qed.

(** Straight-line bodies are more efficiently refined as lists of atomic
    statements.  This evaluator removes the impossible non-normal outcome
    branches introduced by a deeply nested [Ssequence]; its soundness theorem
    below still lands in CompCert's ordinary [exec_stmt]. *)
Definition run_flat_atom (ce: composite_env) (array_block: block)
    (limit: Z) (s: statement) (st: flat_state) : option flat_state :=
  match run_flat_fuel 2 ce array_block limit s st with
  | Some (st', Out_normal) => Some st'
  | _ => None
  end.

Fixpoint run_flat_atoms (ce: composite_env) (array_block: block)
    (limit: Z) (xs: list statement) (st: flat_state) : option flat_state :=
  match xs with
  | nil => Some st
  | x :: rest =>
      match run_flat_atom ce array_block limit x st with
      | Some st' => run_flat_atoms ce array_block limit rest st'
      | None => None
      end
  end.

Lemma run_flat_atoms_app : forall ce array_block limit xs ys st,
  run_flat_atoms ce array_block limit (xs ++ ys) st =
  match run_flat_atoms ce array_block limit xs st with
  | Some mid => run_flat_atoms ce array_block limit ys mid
  | None => None
  end.
Proof.
  intros ce array_block limit xs.
  induction xs as [|x rest IH]; intros ys st; simpl; [reflexivity|].
  destruct (run_flat_atom ce array_block limit x st); simpl; auto.
Qed.

Fixpoint sequence_atoms (xs: list statement) : statement :=
  match xs with
  | nil => Sskip
  | x :: rest => Ssequence x (sequence_atoms rest)
  end.

Fixpoint flatten_sequence (s: statement) : list statement :=
  match s with
  | Ssequence s1 s2 => flatten_sequence s1 ++ flatten_sequence s2
  | _ => s :: nil
  end.

Theorem run_flat_atom_sim :
  forall fe ge e ce array_block limit s flat m flat',
  ce = genv_cenv ge ->
  flat_stmt_supported s = true ->
  flat_block_rel flat.(flat_array) m array_block limit ->
  run_flat_atom ce array_block limit s flat = Some flat' ->
  exists m',
    ClightBigstep.exec_stmt fe ge e flat.(flat_temps) m s E0
      flat'.(flat_temps) m' Out_normal /\
    flat_block_rel flat'.(flat_array) m' array_block limit.
Proof.
  intros fe ge e ce array_block limit s flat m flat' CE SAFE REL RUN.
  unfold run_flat_atom in RUN.
  destruct (run_flat_fuel 2 ce array_block limit s flat)
    as [[candidate out]|] eqn:STEP; try discriminate.
  destruct out; try discriminate. inversion RUN; subst candidate.
  destruct (run_flat_fuel_sim 2 ce array_block limit s flat m flat'
    Out_normal SAFE REL STEP) as [m' [MEMRUN REL']].
  exists m'. split.
  - subst ce. eapply run_mem_fuel_sound; exact MEMRUN.
  - exact REL'.
Qed.

Theorem run_flat_atoms_sim :
  forall fe ge e ce array_block limit xs flat m flat',
  ce = genv_cenv ge ->
  Forall (fun s => flat_stmt_supported s = true) xs ->
  flat_block_rel flat.(flat_array) m array_block limit ->
  run_flat_atoms ce array_block limit xs flat = Some flat' ->
  exists m',
    ClightBigstep.exec_stmt fe ge e flat.(flat_temps) m
      (sequence_atoms xs) E0
      flat'.(flat_temps) m' Out_normal /\
    flat_block_rel flat'.(flat_array) m' array_block limit.
Proof.
  intros fe ge e ce array_block limit xs.
  induction xs as [|x rest IH]; intros flat m flat' CE SAFE REL RUN.
  - simpl in RUN. inversion RUN; subst flat'.
    exists m. split; [constructor | exact REL].
  - simpl in RUN.
    inversion SAFE as [|? ? SAFEX SAFEREST].
    destruct (run_flat_atom ce array_block limit x flat)
      as [mid|] eqn:HEAD; try discriminate.
    destruct (run_flat_atom_sim fe ge e ce array_block limit x flat m mid
      CE SAFEX REL HEAD) as [m1 [EXEC1 REL1]].
    destruct (IH mid m1 flat' CE SAFEREST REL1 RUN)
      as [m' [EXEC2 REL2]].
    exists m'. split.
    + replace E0 with (E0 ** E0) by reflexivity.
      eapply exec_Sseq_1; eauto.
    + exact REL2.
Qed.

(** Execute a flattened straight-line statement without changing the
    association of [Ssequence] in the semantic conclusion.  This is the
    bridge used by staged certificates: computation uses a list, while the
    theorem still names the exact Clight AST. *)
Theorem run_flatten_sequence_sim :
  forall fe ge e ce array_block limit s flat m flat',
  ce = genv_cenv ge ->
  flat_stmt_supported s = true ->
  flat_block_rel flat.(flat_array) m array_block limit ->
  run_flat_atoms ce array_block limit (flatten_sequence s) flat = Some flat' ->
  exists m',
    ClightBigstep.exec_stmt fe ge e flat.(flat_temps) m s E0
      flat'.(flat_temps) m' Out_normal /\
    flat_block_rel flat'.(flat_array) m' array_block limit.
Proof.
  intros fe ge e ce array_block limit s.
  induction s; intros flat m flat' CE SAFE REL RUN;
    try (cbn [flatten_sequence run_flat_atoms] in RUN;
         destruct (run_flat_atom ce array_block limit _ flat)
           as [mid|] eqn:ATOM; try discriminate;
         inversion RUN; subst mid;
         eapply run_flat_atom_sim; eauto).
  cbn [flatten_sequence] in RUN.
  rewrite run_flat_atoms_app in RUN.
  destruct (run_flat_atoms ce array_block limit (flatten_sequence s1) flat)
    as [mid|] eqn:RUN1; try discriminate.
  cbn in SAFE. apply andb_prop in SAFE as [SAFE1 SAFE2].
  destruct (IHs1 flat m mid CE SAFE1 REL RUN1) as [m1 [EXEC1 REL1]].
  destruct (IHs2 mid m1 flat' CE SAFE2 REL1 RUN) as [m2 [EXEC2 REL2]].
  exists m2. split; [|exact REL2].
  replace E0 with (E0 ** E0) by reflexivity.
  eapply exec_Sseq_1; eauto.
Qed.

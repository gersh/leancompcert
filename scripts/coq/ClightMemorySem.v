(* ClightMemorySem.v

   A computable, fuelled evaluator for structured scalar Clight plus the
   memory operations needed by the single-array bridge.  In addition to
   numeric temporaries and rolled loops, this evaluator accepts pointer values,
   casts, and full-width loads and stores through [Ederef].

   The evaluator uses CompCert's own [sem_binary_operation], [sem_cast],
   [Mem.loadv], and [Mem.storev].  Consequently its soundness theorem is about
   the real CompCert memory model, not a second flat-memory approximation.

   Important: soundness does not imply that every syntactically accepted term
   successfully evaluates.  CompCert rejects arithmetic on a [Vptr] when both
   source expressions are typed [tulong].  The array bridge therefore keeps
   its base pointer-typed and emits [base[index]]; the regression file proves
   that this pointer-indexed shape evaluates and instantiates the theorem
   below. *)

From compcert Require Import Coqlib Maps Integers Values Events Memory.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep.

(* ------------------------------------------------------------------ *)
(* Relation between the Lean bridge's flat array and one CompCert block. *)

Definition flat_mem : Type := Z -> option Z.

Definition flat_set (a: flat_mem) (addr value: Z) : flat_mem :=
  fun candidate => if Z.eq_dec candidate addr then Some value else a candidate.

Definition flat_u64_key (base index: Z) : Z := index * 8 + base.
Definition block_u64_ofs (base index: Z) : Z := base + index * 8.

(** A bounded prefix of the Lean flat memory is represented by consecutive
    [Mint64] cells in one CompCert block.  Values are kept in the range where
    [Int64.repr] is injective, matching the Lean register invariant. *)
Definition u64_array_rel (a: flat_mem) (flat_base: Z)
    (m: mem) (b: block) (block_base length: Z) : Prop :=
  forall index,
    0 <= index < length ->
    exists value,
      a (flat_u64_key flat_base index) = Some value /\
      0 <= value < Int64.modulus /\
      Mem.load Mint64 m b (block_u64_ofs block_base index) =
        Some (Vlong (Int64.repr value)).

Lemma flat_u64_key_inj : forall base i j,
  flat_u64_key base i = flat_u64_key base j -> i = j.
Proof. unfold flat_u64_key; intros; lia. Qed.

Lemma u64_array_rel_load : forall a flat_base m b block_base length index,
  u64_array_rel a flat_base m b block_base length ->
  0 <= index < length ->
  exists value,
    a (flat_u64_key flat_base index) = Some value /\
    0 <= value < Int64.modulus /\
    Mem.load Mint64 m b (block_u64_ofs block_base index) =
      Some (Vlong (Int64.repr value)).
Proof. intros; eauto. Qed.

(** A successful CompCert store at a related cell preserves the relation
    after the corresponding flat-memory update.  The proof uses CompCert's
    same-cell and disjoint-load theorems; eight-byte spacing prevents a store
    from changing any other logical cell. *)
Theorem u64_array_rel_store :
  forall a flat_base m b block_base length index value m',
  u64_array_rel a flat_base m b block_base length ->
  0 <= index < length ->
  0 <= value < Int64.modulus ->
  Mem.store Mint64 m b (block_u64_ofs block_base index)
    (Vlong (Int64.repr value)) = Some m' ->
  u64_array_rel
    (flat_set a (flat_u64_key flat_base index) value)
    flat_base m' b block_base length.
Proof.
  intros a flat_base m b block_base length index value m'
    REL HINDEX HVALUE STORE.
  intros other HOTHER.
  destruct (Z.eq_dec other index) as [SAME|DIFF].
  - subst other. exists value. split.
    + unfold flat_set. destruct (Z.eq_dec
        (flat_u64_key flat_base index) (flat_u64_key flat_base index));
        congruence.
    + split; auto.
      pose proof (Mem.load_store_same Mint64 m b
        (block_u64_ofs block_base index) (Vlong (Int64.repr value)) m'
        STORE) as LOAD.
      cbn in LOAD. exact LOAD.
  - destruct (REL other HOTHER) as [old [FLAT [HOLD LOAD]]].
    exists old. split.
    + unfold flat_set.
      destruct (Z.eq_dec (flat_u64_key flat_base other)
        (flat_u64_key flat_base index)) as [KEYS|KEYS].
      * exfalso. apply DIFF. now apply flat_u64_key_inj in KEYS.
      * exact FLAT.
    + split; auto.
      pose proof (Mem.load_store_other Mint64 m b
        (block_u64_ofs block_base index) (Vlong (Int64.repr value)) m'
        STORE Mint64 b (block_u64_ofs block_base other)) as OTHER.
      rewrite OTHER; auto.
      right. unfold block_u64_ofs. simpl.
      destruct (Z_lt_ge_dec other index).
      * left; lia.
      * right; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Expressions, including full-width dereference loads. *)

Fixpoint eval_mem (ce: composite_env) (m: mem) (le: temp_env) (a: expr)
    : option val :=
  match a with
  | Econst_int i _ => Some (Vint i)
  | Econst_long i _ => Some (Vlong i)
  | Etempvar id _ => PTree.get id le
  | Ederef addr ty =>
      match eval_mem ce m le addr with
      | Some (Vptr b ofs) =>
          match access_mode ty with
          | By_value chunk => Mem.loadv chunk m (Vptr b ofs)
          | _ => None
          end
      | _ => None
      end
  | Ebinop op a1 a2 _ =>
      match eval_mem ce m le a1, eval_mem ce m le a2 with
      | Some v1, Some v2 =>
          sem_binary_operation ce op v1 (typeof a1) v2 (typeof a2) m
      | _, _ => None
      end
  | Ecast a1 ty =>
      match eval_mem ce m le a1 with
      | Some v1 => sem_cast v1 (typeof a1) ty m
      | None => None
      end
  | _ => None
  end.

(** A computable syntactic check for the exact expression/statement fragment
    handled by [eval_mem]/[run_mem_fuel].  Per-artifact checks use this to
    ensure a production Clight body contains no silently unsupported form. *)
Fixpoint mem_expr_supported (a: expr) : bool :=
  match a with
  | Econst_int _ _ | Econst_long _ _ | Etempvar _ _ => true
  | Ederef addr _ => mem_expr_supported addr
  | Ebinop _ a1 a2 _ => mem_expr_supported a1 && mem_expr_supported a2
  | Ecast a1 _ => mem_expr_supported a1
  | _ => false
  end.

Fixpoint mem_stmt_supported (s: statement) : bool :=
  match s with
  | Sskip | Sbreak | Scontinue => true
  | Sassign (Ederef addr _) rhs =>
      mem_expr_supported addr && mem_expr_supported rhs
  | Sassign _ _ => false
  | Sset _ a => mem_expr_supported a
  | Ssequence s1 s2 => mem_stmt_supported s1 && mem_stmt_supported s2
  | Sifthenelse a s1 s2 =>
      mem_expr_supported a && mem_stmt_supported s1 && mem_stmt_supported s2
  | Sloop s1 s2 => mem_stmt_supported s1 && mem_stmt_supported s2
  | Sreturn None => true
  | Sreturn (Some a) => mem_expr_supported a
  | _ => false
  end.

Lemma eval_mem_sound:
  forall ge en le m a v,
  eval_mem (genv_cenv ge) m le a = Some v ->
  eval_expr ge en le m a v.
Proof.
  intros ge en le m a; induction a; simpl; intros v H; try discriminate.
  - inversion H; subst. apply eval_Econst_int.
  - inversion H; subst. apply eval_Econst_long.
  - now apply eval_Etempvar.
  - destruct (eval_mem (genv_cenv ge) m le a) as [va|] eqn:EA;
      try discriminate.
    destruct va; simpl in H; try discriminate H.
    destruct (access_mode t) eqn:AM.
    + eapply eval_Elvalue.
      * apply eval_Ederef. apply IHa. reflexivity.
      * eapply deref_loc_value with (chunk := m0); eauto.
    + discriminate H.
    + discriminate H.
    + discriminate H.
  - destruct (eval_mem (genv_cenv ge) m le a1) as [v1|] eqn:E1;
      try discriminate.
    destruct (eval_mem (genv_cenv ge) m le a2) as [v2|] eqn:E2;
      try discriminate.
    destruct (sem_binary_operation (genv_cenv ge) b v1 (typeof a1)
      v2 (typeof a2) m) as [vres|] eqn:SEM; try discriminate.
    inversion H; subst. eapply eval_Ebinop; eauto.
  - destruct (eval_mem (genv_cenv ge) m le a) as [v1|] eqn:E1;
      try discriminate.
    destruct (sem_cast v1 (typeof a) t m) as [vres|] eqn:CAST;
      try discriminate.
    inversion H; subst. eapply eval_Ecast; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Statements.  [Sassign] is restricted to the exact full-width [Ederef]
   lvalue emitted for array load/store instructions. *)

Fixpoint run_mem_fuel (fuel: nat) (ce: composite_env) (m: mem)
    (s: statement) (le: temp_env)
    : option (temp_env * (mem * outcome)) :=
  match fuel with
  | O => None
  | S fuel' =>
      match s with
      | Sskip => Some (le, (m, Out_normal))
      | Sassign (Ederef addr ty) rhs =>
          match eval_mem ce m le addr with
          | Some (Vptr b ofs) =>
              match eval_mem ce m le rhs with
              | Some v2 =>
                  match sem_cast v2 (typeof rhs) ty m with
                  | Some v =>
                      match access_mode ty with
                      | By_value chunk =>
                          match Mem.storev chunk m (Vptr b ofs) v with
                          | Some m' => Some (le, (m', Out_normal))
                          | None => None
                          end
                      | _ => None
                      end
                  | None => None
                  end
              | None => None
              end
          | _ => None
          end
      | Sassign _ _ => None
      | Sset id a =>
          match eval_mem ce m le a with
          | Some v => Some (PTree.set id v le, (m, Out_normal))
          | None => None
          end
      | Ssequence s1 s2 =>
          match run_mem_fuel fuel' ce m s1 le with
          | Some (le1, (m1, Out_normal)) =>
              run_mem_fuel fuel' ce m1 s2 le1
          | res => res
          end
      | Sifthenelse a s1 s2 =>
          match eval_mem ce m le a with
          | Some v =>
              match bool_val v (typeof a) m with
              | Some b =>
                  run_mem_fuel fuel' ce m (if b then s1 else s2) le
              | None => None
              end
          | None => None
          end
      | Sloop s1 s2 =>
          match run_mem_fuel fuel' ce m s1 le with
          | Some (le1, (m1, Out_break)) =>
              Some (le1, (m1, Out_normal))
          | Some (le1, (m1, Out_return ret)) =>
              Some (le1, (m1, Out_return ret))
          | Some (le1, (m1, Out_normal))
          | Some (le1, (m1, Out_continue)) =>
              match run_mem_fuel fuel' ce m1 s2 le1 with
              | Some (le2, (m2, Out_break)) =>
                  Some (le2, (m2, Out_normal))
              | Some (le2, (m2, Out_return ret)) =>
                  Some (le2, (m2, Out_return ret))
              | Some (le2, (m2, Out_normal)) =>
                  run_mem_fuel fuel' ce m2 (Sloop s1 s2) le2
              | Some (_, (_, Out_continue)) => None
              | None => None
              end
          | None => None
          end
      | Sbreak => Some (le, (m, Out_break))
      | Scontinue => Some (le, (m, Out_continue))
      | Sreturn None => Some (le, (m, Out_return None))
      | Sreturn (Some a) =>
          match eval_mem ce m le a with
          | Some v => Some (le, (m, Out_return (Some (v, typeof a))))
          | None => None
          end
      | _ => None
      end
  end.

(** A successful memory-aware run is an execution in CompCert's actual
    Clight big-step semantics.  This one theorem covers straight-line scalar,
    rolled scalar, and CompCert-defined pointer-backed statement bodies. *)
Theorem run_mem_fuel_sound:
  forall fuel fe ge en m s le le' m' out,
  run_mem_fuel fuel (genv_cenv ge) m s le = Some (le', (m', out)) ->
  ClightBigstep.exec_stmt fe ge en le m s E0 le' m' out.
Proof.
  induction fuel as [|fuel IH]; intros fe ge en m s le le' m' out H.
  - discriminate.
  - destruct s; simpl in H; try discriminate.
    + (* Sskip *)
      inversion H; subst. apply exec_Sskip.
    + (* Sassign *)
      destruct e; try discriminate.
      destruct (eval_mem (genv_cenv ge) m le e) as [va|] eqn:EA;
        try discriminate.
      destruct va; simpl in H; try discriminate.
      destruct (eval_mem (genv_cenv ge) m le e0) as [v2|] eqn:E2;
        try discriminate.
      destruct (sem_cast v2 (typeof e0) t m) as [v|] eqn:CAST;
        try discriminate.
      destruct (access_mode t) eqn:AM; simpl in H; try discriminate.
      destruct (Mem.store m0 m b (Ptrofs.unsigned i) v) as [m1|] eqn:STORE;
        try discriminate.
      inversion H; subst.
      eapply exec_Sassign with (loc := b) (ofs := i) (bf := Full)
        (v2 := v2) (v := v).
      * apply eval_Ederef. now apply eval_mem_sound.
      * now apply eval_mem_sound.
      * exact CAST.
      * eapply assign_loc_value with (chunk := m0); eauto.
    + (* Sset *)
      destruct (eval_mem (genv_cenv ge) m le e) as [v|] eqn:E;
        try discriminate.
      inversion H; subst. apply exec_Sset. now apply eval_mem_sound.
    + (* Ssequence *)
      destruct (run_mem_fuel fuel (genv_cenv ge) m s1 le)
        as [[le1 [m1 out1]]|] eqn:R1; try discriminate.
      destruct out1.
      * inversion H; subst. eapply exec_Sseq_2.
        -- eapply IH; eauto.
        -- discriminate.
      * inversion H; subst. eapply exec_Sseq_2.
        -- eapply IH; eauto.
        -- discriminate.
      * change E0 with (E0 ** E0). eapply exec_Sseq_1.
        -- eapply IH; eauto.
        -- eapply IH; eauto.
      * inversion H; subst. eapply exec_Sseq_2.
        -- eapply IH; eauto.
        -- discriminate.
    + (* Sifthenelse *)
      destruct (eval_mem (genv_cenv ge) m le e) as [v|] eqn:E;
        try discriminate.
      destruct (bool_val v (typeof e) m) as [b|] eqn:B;
        try discriminate.
      eapply exec_Sifthenelse with (v1 := v) (b := b).
      * now apply eval_mem_sound.
      * exact B.
      * eapply IH; eauto.
    + (* Sloop *)
      destruct (run_mem_fuel fuel (genv_cenv ge) m s1 le)
        as [[le1 [m1 out1]]|] eqn:R1; try discriminate.
      destruct out1.
      * inversion H; subst. eapply exec_Sloop_stop1.
        -- eapply IH; eauto.
        -- constructor.
      * destruct (run_mem_fuel fuel (genv_cenv ge) m1 s2 le1)
          as [[le2 [m2 out2]]|] eqn:R2; try discriminate.
        destruct out2.
        -- inversion H; subst. change E0 with (E0 ** E0).
           eapply exec_Sloop_stop2;
             [eapply IH; eauto | constructor | eapply IH; eauto | constructor].
        -- discriminate.
        -- change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop;
             [eapply IH; eauto | constructor | eapply IH; eauto
             | eapply IH; eauto].
        -- inversion H; subst. change E0 with (E0 ** E0).
           eapply exec_Sloop_stop2;
             [eapply IH; eauto | constructor | eapply IH; eauto | constructor].
      * destruct (run_mem_fuel fuel (genv_cenv ge) m1 s2 le1)
          as [[le2 [m2 out2]]|] eqn:R2; try discriminate.
        destruct out2.
        -- inversion H; subst. change E0 with (E0 ** E0).
           eapply exec_Sloop_stop2;
             [eapply IH; eauto | constructor | eapply IH; eauto | constructor].
        -- discriminate.
        -- change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop;
             [eapply IH; eauto | constructor | eapply IH; eauto
             | eapply IH; eauto].
        -- inversion H; subst. change E0 with (E0 ** E0).
           eapply exec_Sloop_stop2;
             [eapply IH; eauto | constructor | eapply IH; eauto | constructor].
      * inversion H; subst. eapply exec_Sloop_stop1.
        -- eapply IH; eauto.
        -- constructor.
    + (* Sbreak *)
      inversion H; subst. apply exec_Sbreak.
    + (* Scontinue *)
      inversion H; subst. apply exec_Scontinue.
    + (* Sreturn *)
      destruct o as [a|].
      * destruct (eval_mem (genv_cenv ge) m le a) as [v|] eqn:E;
          try discriminate.
        inversion H; subst. apply exec_Sreturn_some.
        now apply eval_mem_sound.
      * inversion H; subst. apply exec_Sreturn_none.
Qed.

(** Function-call form for Clight2.  Unlike the scalar-only corollary, this
    version accepts parameter temporaries, so a single pointer argument can
    name the CompCert block representing the certificate's abstract array. *)
Corollary run_mem_fuel_funcall2:
  forall fuel ge f vargs m le0 le' m' v ty vres,
  fn_vars f = nil ->
  list_norepet (var_names (fn_params f)) ->
  list_disjoint (var_names (fn_params f)) (var_names (fn_temps f)) ->
  bind_parameter_temps (fn_params f) vargs
    (create_undef_temps (fn_temps f)) = Some le0 ->
  fn_return f <> Tvoid ->
  run_mem_fuel fuel (genv_cenv ge) m (fn_body f) le0 =
    Some (le', (m', Out_return (Some (v, ty)))) ->
  sem_cast v ty (fn_return f) m' = Some vres ->
  ClightBigstep.eval_funcall function_entry2 ge m
    (Internal f) vargs E0 m' vres.
Proof.
  intros fuel ge f vargs m le0 le' m' v ty vres
    VARS PARAMS DISJOINT BIND RET RUN CAST.
  eapply eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m').
  - constructor.
    + rewrite VARS; constructor.
    + exact PARAMS.
    + exact DISJOINT.
    + rewrite VARS; constructor.
    + exact BIND.
  - eapply run_mem_fuel_sound; eauto.
  - simpl; auto.
  - reflexivity.
Qed.

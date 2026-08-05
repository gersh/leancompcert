(* ClightFragmentSem.v

   A computable evaluator for a goto-free, memory-free, integer-only
   fragment of Clight (statements: Sskip, Sset, Ssequence, Sreturn;
   expressions: Etempvar, Econst_int, Econst_long, Ebinop, Ecast),
   together with a soundness proof against CompCert's big-step
   semantics (cfrontend/ClightBigstep.v).

   Design notes:
   - [eval_e] calls CompCert's own semantic functions
     [Cop.sem_binary_operation] and [Cop.sem_cast], parameterized by a
     composite env [ce] and a memory [m], so soundness per case is a
     direct constructor application.
   - Results are guarded to be [Vint]/[Vlong] ([num_val]), and binary
     operators are guarded to the non-pointer classify cases
     ([binop_ok]).  Under these guards the evaluator is provably
     independent of both [ce] and [m] ([eval_e_indep], [run_indep]),
     so a single vm_compute run with [PTree.empty composite] and
     [Mem.empty] yields conclusions for EVERY genv and EVERY memory.
   - [run] threads the memory through unchanged: the fragment never
     writes memory, matching the exec_stmt instances it produces
     (initial memory = final memory), and all traces are E0.
   - The statement-level theorems [run_sound] and [run_fuel_sound] are generic in the
     [function_entry] family (our statements contain no calls).  The
     function-level corollaries [run_funcall2] and [run_fuel_funcall2] are stated against
     [function_entry2] (Clight2: parameters as temporaries), which is
     the right entry semantics for functions with fn_params = fn_vars
     = nil and everything in temps. *)

From compcert Require Import Coqlib Maps Integers Values Events Memory.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep.

Local Open Scope error_monad_scope.

(* ------------------------------------------------------------------ *)
(* Value and operator guards *)

Definition is_num (v: val) : bool :=
  match v with
  | Vint _ => true
  | Vlong _ => true
  | _ => false
  end.

Definition num_val (v: val) : option val :=
  if is_num v then Some v else None.

Lemma num_val_some:
  forall v v', num_val v = Some v' -> v' = v /\ is_num v = true.
Proof.
  unfold num_val; intros v v' H.
  destruct (is_num v); inversion H; auto.
Qed.

(* Restrict binary operators to the classify cases whose semantics
   consult neither the composite environment nor the memory (given
   Vint/Vlong operands): the sem_binarith / sem_shift code paths. *)

Definition binop_ok (op: binary_operation) (t1 t2: type) : bool :=
  match op with
  | Oadd => match classify_add t1 t2 with add_default => true | _ => false end
  | Osub => match classify_sub t1 t2 with sub_default => true | _ => false end
  | Omul | Odiv | Omod | Oand | Oor | Oxor => true
  | Oshl | Oshr => true
  | Oeq | One | Olt | Ogt | Ole | Oge =>
      match classify_cmp t1 t2 with cmp_default => true | _ => false end
  end.

(* ------------------------------------------------------------------ *)
(* Computable expression evaluator *)

Fixpoint eval_e (ce: composite_env) (m: mem) (le: temp_env) (a: expr)
    : option val :=
  match a with
  | Econst_int i _ => Some (Vint i)
  | Econst_long i _ => Some (Vlong i)
  | Etempvar id _ =>
      match PTree.get id le with
      | Some v => num_val v
      | None => None
      end
  | Ebinop op a1 a2 _ =>
      if binop_ok op (typeof a1) (typeof a2) then
        match eval_e ce m le a1, eval_e ce m le a2 with
        | Some v1, Some v2 =>
            match sem_binary_operation ce op v1 (typeof a1) v2 (typeof a2) m with
            | Some v => num_val v
            | None => None
            end
        | _, _ => None
        end
      else None
  | Ecast a1 ty =>
      match eval_e ce m le a1 with
      | Some v1 =>
          match sem_cast v1 (typeof a1) ty m with
          | Some v => num_val v
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

(* ------------------------------------------------------------------ *)
(* Computable statement runner.  Outcomes are CompCert's own
   [ClightBigstep.outcome].  Memory is threaded through unchanged. *)

Fixpoint run (ce: composite_env) (m: mem) (s: statement) (le: temp_env)
    : option (temp_env * outcome) :=
  match s with
  | Sskip => Some (le, Out_normal)
  | Sset id a =>
      match eval_e ce m le a with
      | Some v => Some (PTree.set id v le, Out_normal)
      | None => None
      end
  | Ssequence s1 s2 =>
      match run ce m s1 le with
      | Some (le1, Out_normal) => run ce m s2 le1
      | res => res
      end
  | Sreturn None => Some (le, Out_return None)
  | Sreturn (Some a) =>
      match eval_e ce m le a with
      | Some v => Some (le, Out_return (Some (v, typeof a)))
      | None => None
      end
  | _ => None
  end.

(* Projection used by per-certificate checks: a closed term suitable
   for vm_compute (no existential over the final temp env). *)

Definition run_ret (ce: composite_env) (m: mem) (s: statement) (le: temp_env)
    : option (val * type) :=
  match run ce m s le with
  | Some (_, Out_return (Some vt)) => Some vt
  | _ => None
  end.

Lemma run_ret_run:
  forall ce m s le vt,
  run_ret ce m s le = Some vt ->
  exists le', run ce m s le = Some (le', Out_return (Some vt)).
Proof.
  unfold run_ret; intros ce m s le vt H.
  destruct (run ce m s le) as [[le' out]|]; try discriminate.
  destruct out; try discriminate.
  destruct o; inversion H; subst; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Fuelled control-flow runner.

   [run] above deliberately has the smallest possible statement language: it
   is the fast evaluator used by the original straight-line direct-emission
   gate.  Production certificates are normally emitted in the rolled form,
   however, and [Clight.Swhile] elaborates to [Sloop]/[Sifthenelse]/[Sbreak].

   [run_fuel] is the generic control-flow layer.  It keeps the same guarded
   expression evaluator, threads memory (unchanged for this numeric fragment),
   and supports exactly the structured control flow needed by a rolled scalar
   certificate.  Fuel is a proof/checking resource, not source semantics: each
   recursive descent and each loop iteration consumes one unit.  A successful
   result is therefore a finite execution certificate that the theorem below
   carries into CompCert's actual big-step semantics. *)

Fixpoint run_fuel (fuel: nat) (ce: composite_env) (m: mem)
    (s: statement) (le: temp_env)
    : option (temp_env * (mem * outcome)) :=
  match fuel with
  | O => None
  | S fuel' =>
      match s with
      | Sskip => Some (le, (m, Out_normal))
      | Sset id a =>
          match eval_e ce m le a with
          | Some v => Some (PTree.set id v le, (m, Out_normal))
          | None => None
          end
      | Ssequence s1 s2 =>
          match run_fuel fuel' ce m s1 le with
          | Some (le1, (m1, Out_normal)) => run_fuel fuel' ce m1 s2 le1
          | res => res
          end
      | Sifthenelse a s1 s2 =>
          match eval_e ce m le a with
          | Some v =>
              match bool_val v (typeof a) m with
              | Some b => run_fuel fuel' ce m (if b then s1 else s2) le
              | None => None
              end
          | None => None
          end
      | Sloop s1 s2 =>
          match run_fuel fuel' ce m s1 le with
          | Some (le1, (m1, Out_break)) =>
              Some (le1, (m1, Out_normal))
          | Some (le1, (m1, Out_return ret)) =>
              Some (le1, (m1, Out_return ret))
          | Some (le1, (m1, Out_normal))
          | Some (le1, (m1, Out_continue)) =>
              match run_fuel fuel' ce m1 s2 le1 with
              | Some (le2, (m2, Out_break)) =>
                  Some (le2, (m2, Out_normal))
              | Some (le2, (m2, Out_return ret)) =>
                  Some (le2, (m2, Out_return ret))
              | Some (le2, (m2, Out_normal)) =>
                  run_fuel fuel' ce m2 (Sloop s1 s2) le2
              | Some (_, (_, Out_continue)) => None
              | None => None
              end
          | None => None
          end
      | Sbreak => Some (le, (m, Out_break))
      | Scontinue => Some (le, (m, Out_continue))
      | Sreturn None => Some (le, (m, Out_return None))
      | Sreturn (Some a) =>
          match eval_e ce m le a with
          | Some v => Some (le, (m, Out_return (Some (v, typeof a))))
          | None => None
          end
      | _ => None
      end
  end.

(* ------------------------------------------------------------------ *)
(* Soundness of eval_e against Clight.eval_expr *)

Lemma eval_e_sound:
  forall ge en le m a v,
  eval_e (genv_cenv ge) m le a = Some v ->
  eval_expr ge en le m a v.
Proof.
  intros ge en le m a; induction a; simpl; intros v H; try discriminate.
  - (* Econst_int *)
    inversion H; subst. apply eval_Econst_int.
  - (* Econst_long *)
    inversion H; subst. apply eval_Econst_long.
  - (* Etempvar *)
    destruct (PTree.get i le) as [v0|] eqn:G; try discriminate.
    apply num_val_some in H. destruct H as [-> _].
    apply eval_Etempvar; auto.
  - (* Ebinop *)
    destruct (binop_ok b (typeof a1) (typeof a2)); try discriminate.
    destruct (eval_e (genv_cenv ge) m le a1) as [v1|] eqn:E1; try discriminate.
    destruct (eval_e (genv_cenv ge) m le a2) as [v2|] eqn:E2; try discriminate.
    destruct (sem_binary_operation (genv_cenv ge) b v1 (typeof a1) v2 (typeof a2) m)
      as [v0|] eqn:B; try discriminate.
    apply num_val_some in H. destruct H as [-> _].
    eapply eval_Ebinop; eauto.
  - (* Ecast *)
    destruct (eval_e (genv_cenv ge) m le a) as [v1|] eqn:E1; try discriminate.
    destruct (sem_cast v1 (typeof a) t m) as [v0|] eqn:C; try discriminate.
    apply num_val_some in H. destruct H as [-> _].
    eapply eval_Ecast; eauto.
Qed.

(* Every value produced by eval_e is a Vint or Vlong. *)

Lemma eval_e_num:
  forall ce m le a v, eval_e ce m le a = Some v -> is_num v = true.
Proof.
  intros ce m le a v H; destruct a; simpl in H; try discriminate.
  - inversion H; subst; reflexivity.
  - inversion H; subst; reflexivity.
  - destruct (PTree.get i le) as [v0|]; try discriminate.
    apply num_val_some in H; destruct H as [-> ?]; auto.
  - destruct (binop_ok b (typeof a1) (typeof a2)); try discriminate.
    destruct (eval_e ce m le a1); try discriminate.
    destruct (eval_e ce m le a2); try discriminate.
    destruct (sem_binary_operation ce b v0 (typeof a1) v1 (typeof a2) m);
      try discriminate.
    apply num_val_some in H; destruct H as [-> ?]; auto.
  - destruct (eval_e ce m le a); try discriminate.
    destruct (sem_cast v0 (typeof a) t m); try discriminate.
    apply num_val_some in H; destruct H as [-> ?]; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Memory / composite-env independence of the guarded fragment *)

Lemma sem_cast_indep:
  forall v t1 t2 m m',
  is_num v = true ->
  sem_cast v t1 t2 m = sem_cast v t1 t2 m'.
Proof.
  intros v t1 t2 m m' H.
  destruct v; try discriminate;
  unfold sem_cast; destruct (classify_cast t1 t2); reflexivity.
Qed.

Lemma sem_binarith_indep:
  forall si sl sf ss v1 t1 v2 t2 m m',
  is_num v1 = true -> is_num v2 = true ->
  sem_binarith si sl sf ss v1 t1 v2 t2 m
    = sem_binarith si sl sf ss v1 t1 v2 t2 m'.
Proof.
  intros; unfold sem_binarith.
  rewrite (sem_cast_indep v1 t1 _ m m') by auto.
  rewrite (sem_cast_indep v2 t2 _ m m') by auto.
  reflexivity.
Qed.

Lemma sem_binop_indep:
  forall ce ce' op v1 t1 v2 t2 m m',
  binop_ok op t1 t2 = true ->
  is_num v1 = true -> is_num v2 = true ->
  sem_binary_operation ce op v1 t1 v2 t2 m
    = sem_binary_operation ce' op v1 t1 v2 t2 m'.
Proof.
  intros ce ce' op v1 t1 v2 t2 m m' OK N1 N2.
  destruct op; simpl in OK |- *;
  unfold sem_add, sem_sub, sem_mul, sem_div, sem_mod,
         sem_and, sem_or, sem_xor, sem_shl, sem_shr, sem_cmp;
  try (apply sem_binarith_indep; auto; fail);
  try reflexivity.
  - destruct (classify_add t1 t2); try discriminate;
      apply sem_binarith_indep; auto.
  - destruct (classify_sub t1 t2); try discriminate;
      apply sem_binarith_indep; auto.
  - destruct (classify_cmp t1 t2); try discriminate;
      apply sem_binarith_indep; auto.
  - destruct (classify_cmp t1 t2); try discriminate;
      apply sem_binarith_indep; auto.
  - destruct (classify_cmp t1 t2); try discriminate;
      apply sem_binarith_indep; auto.
  - destruct (classify_cmp t1 t2); try discriminate;
      apply sem_binarith_indep; auto.
  - destruct (classify_cmp t1 t2); try discriminate;
      apply sem_binarith_indep; auto.
  - destruct (classify_cmp t1 t2); try discriminate;
      apply sem_binarith_indep; auto.
Qed.

Lemma eval_e_indep:
  forall a ce ce' m m' le,
  eval_e ce m le a = eval_e ce' m' le a.
Proof.
  induction a; intros ce ce' m m' le; simpl; auto.
  - (* Ebinop *)
    destruct (binop_ok b (typeof a1) (typeof a2)) eqn:OK; auto.
    rewrite (IHa1 ce ce' m m' le), (IHa2 ce ce' m m' le).
    destruct (eval_e ce' m' le a1) as [v1|] eqn:E1; auto.
    destruct (eval_e ce' m' le a2) as [v2|] eqn:E2; auto.
    rewrite (sem_binop_indep ce ce' b v1 (typeof a1) v2 (typeof a2) m m'); auto.
    + eapply eval_e_num; eauto.
    + eapply eval_e_num; eauto.
  - (* Ecast *)
    rewrite (IHa ce ce' m m' le).
    destruct (eval_e ce' m' le a) as [v1|] eqn:E1; auto.
    rewrite (sem_cast_indep v1 (typeof a) t m m'); auto.
    eapply eval_e_num; eauto.
Qed.

Lemma run_indep:
  forall s ce ce' m m' le,
  run ce m s le = run ce' m' s le.
Proof.
  induction s; intros ce ce' m m' le; simpl; auto.
  - (* Sset *)
    rewrite (eval_e_indep e ce ce' m m' le); auto.
  - (* Ssequence *)
    rewrite (IHs1 ce ce' m m' le).
    destruct (run ce' m' s1 le) as [[le1 out1]|]; auto.
    destruct out1; auto.
  - (* Sreturn *)
    destruct o; auto.
    rewrite (eval_e_indep e ce ce' m m' le); auto.
Qed.

Corollary run_ret_indep:
  forall s ce ce' m m' le,
  run_ret ce m s le = run_ret ce' m' s le.
Proof.
  intros; unfold run_ret; rewrite (run_indep s ce ce' m m' le); auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Soundness of run against ClightBigstep.exec_stmt.

   Generic in the function-entry family [fe] (the fragment contains no
   calls), so it applies to both Clight1 (function_entry1) and Clight2
   (function_entry2) big-step semantics.  All traces are E0 and the
   memory is unchanged. *)

Theorem run_sound:
  forall fe ge en m s le le' out,
  run (genv_cenv ge) m s le = Some (le', out) ->
  ClightBigstep.exec_stmt fe ge en le m s E0 le' m out.
Proof.
  intros fe ge en m s; induction s; intros le le' out H; simpl in H;
    try discriminate.
  - (* Sskip *)
    inversion H; subst. apply exec_Sskip.
  - (* Sset *)
    destruct (eval_e (genv_cenv ge) m le e) as [v|] eqn:E; inversion H; subst.
    apply exec_Sset. apply eval_e_sound; auto.
  - (* Ssequence *)
    destruct (run (genv_cenv ge) m s1 le) as [[le1 out1]|] eqn:R1;
      try discriminate.
    destruct out1.
    + (* Out_break *)
      inversion H; subst.
      apply exec_Sseq_2; auto. discriminate.
    + (* Out_continue *)
      inversion H; subst.
      apply exec_Sseq_2; auto. discriminate.
    + (* Out_normal *)
      change E0 with (E0 ** E0).
      eapply exec_Sseq_1; eauto.
    + (* Out_return *)
      inversion H; subst.
      apply exec_Sseq_2; auto. discriminate.
  - (* Sreturn *)
    destruct o as [a|].
    + destruct (eval_e (genv_cenv ge) m le a) as [v|] eqn:E; inversion H; subst.
      apply exec_Sreturn_some. apply eval_e_sound; auto.
    + inversion H; subst. apply exec_Sreturn_none.
Qed.

(** A successful [run_fuel] computation is a CompCert big-step execution.

    This is the once-and-for-all control-flow theorem used for rolled scalar
    certificates.  It is deliberately stated over the actual Clight statement
    supplied by the caller: after a directly emitted function has elaborated,
    no printer or parser model occurs in the conclusion. *)
Theorem run_fuel_sound:
  forall fuel fe ge en m s le le' m' out,
  run_fuel fuel (genv_cenv ge) m s le = Some (le', (m', out)) ->
  ClightBigstep.exec_stmt fe ge en le m s E0 le' m' out.
Proof.
  induction fuel as [|fuel IH]; intros fe ge en m s le le' m' out H.
  - discriminate.
  - destruct s; simpl in H; try discriminate.
    + (* Sskip *)
      inversion H; subst. apply exec_Sskip.
    + (* Sset *)
      destruct (eval_e (genv_cenv ge) m le e) as [v|] eqn:E;
        try discriminate.
      inversion H; subst. apply exec_Sset. now apply eval_e_sound.
    + (* Ssequence *)
      destruct (run_fuel fuel (genv_cenv ge) m s1 le)
        as [[le1 [m1 out1]]|] eqn:R1; try discriminate.
      destruct out1.
      * inversion H; subst. eapply exec_Sseq_2.
        -- eapply IH; eauto.
        -- discriminate.
      * inversion H; subst. eapply exec_Sseq_2.
        -- eapply IH; eauto.
        -- discriminate.
      * change E0 with (E0 ** E0).
        eapply exec_Sseq_1.
        -- eapply IH; eauto.
        -- eapply IH; eauto.
      * inversion H; subst. eapply exec_Sseq_2.
        -- eapply IH; eauto.
        -- discriminate.
    + (* Sifthenelse *)
      destruct (eval_e (genv_cenv ge) m le e) as [v|] eqn:E;
        try discriminate.
      destruct (bool_val v (typeof e) m) as [b|] eqn:B;
        try discriminate.
      eapply exec_Sifthenelse with (v1 := v) (b := b).
      * now apply eval_e_sound.
      * exact B.
      * eapply IH; eauto.
    + (* Sloop *)
      destruct (run_fuel fuel (genv_cenv ge) m s1 le)
        as [[le1 [m1 out1]]|] eqn:R1; try discriminate.
      destruct out1.
      * (* body breaks *)
        inversion H; subst. eapply exec_Sloop_stop1.
        -- eapply IH; eauto.
        -- constructor.
      * (* body continues *)
        destruct (run_fuel fuel (genv_cenv ge) m1 s2 le1)
          as [[le2 [m2 out2]]|] eqn:R2; try discriminate.
        destruct out2.
        -- inversion H; subst. change E0 with (E0 ** E0).
           eapply exec_Sloop_stop2.
           ++ eapply IH; eauto.
           ++ constructor.
           ++ eapply IH; eauto.
           ++ constructor.
        -- discriminate.
        -- change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop.
           ++ eapply IH; eauto.
           ++ constructor.
           ++ eapply IH; eauto.
           ++ eapply IH; eauto.
        -- inversion H; subst. change E0 with (E0 ** E0).
           eapply exec_Sloop_stop2.
           ++ eapply IH; eauto.
           ++ constructor.
           ++ eapply IH; eauto.
           ++ constructor.
      * (* body is normal *)
        destruct (run_fuel fuel (genv_cenv ge) m1 s2 le1)
          as [[le2 [m2 out2]]|] eqn:R2; try discriminate.
        destruct out2.
        -- inversion H; subst. change E0 with (E0 ** E0).
           eapply exec_Sloop_stop2.
           ++ eapply IH; eauto.
           ++ constructor.
           ++ eapply IH; eauto.
           ++ constructor.
        -- discriminate.
        -- change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop.
           ++ eapply IH; eauto.
           ++ constructor.
           ++ eapply IH; eauto.
           ++ eapply IH; eauto.
        -- inversion H; subst. change E0 with (E0 ** E0).
           eapply exec_Sloop_stop2.
           ++ eapply IH; eauto.
           ++ constructor.
           ++ eapply IH; eauto.
           ++ constructor.
      * (* body returns *)
        inversion H; subst. eapply exec_Sloop_stop1.
        -- eapply IH; eauto.
        -- constructor.
    + (* Sbreak *)
      inversion H; subst. apply exec_Sbreak.
    + (* Scontinue *)
      inversion H; subst. apply exec_Scontinue.
    + (* Sreturn *)
      destruct o as [a|].
      * destruct (eval_e (genv_cenv ge) m le a) as [v|] eqn:E;
          try discriminate.
        inversion H; subst. apply exec_Sreturn_some. now apply eval_e_sound.
      * inversion H; subst. apply exec_Sreturn_none.
Qed.

(* ------------------------------------------------------------------ *)
(* Function-level corollary, against the Clight2 entry semantics
   (function_entry2: parameters as temporaries).  For a function with
   fn_params = fn_vars = nil, entry allocates nothing (env is
   empty_env, memory unchanged) and the initial temp env is
   create_undef_temps (fn_temps f).  Per eval_funcall_internal, the
   returned value is the return-type cast (outcome_result_value) of
   the value computed by the body. *)

Corollary run_funcall2:
  forall ge f m le' v ty vres,
  fn_params f = nil ->
  fn_vars f = nil ->
  fn_return f <> Tvoid ->
  run (genv_cenv ge) m (fn_body f) (create_undef_temps (fn_temps f))
    = Some (le', Out_return (Some (v, ty))) ->
  sem_cast v ty (fn_return f) m = Some vres ->
  ClightBigstep.eval_funcall function_entry2 ge m (Internal f) nil E0 m vres.
Proof.
  intros ge f m le' v ty vres P V R RUN CAST.
  eapply eval_funcall_internal with (e := empty_env) (m2 := m) (m1 := m).
  - (* function_entry2 *)
    constructor.
    + rewrite V; constructor.
    + rewrite P; constructor.
    + rewrite P; red; simpl; tauto.
    + rewrite V; constructor.
    + rewrite P; reflexivity.
  - (* body *)
    eapply run_sound; eauto.
  - (* outcome_result_value: fn_return <> Tvoid /\ return-type cast *)
    simpl; auto.
  - (* free_list of an empty env *)
    reflexivity.
Qed.

(** Function-level form of [run_fuel_sound].  This is the generic theorem a
    rolled scalar certificate instantiates: the certificate supplies its
    concrete Clight [function], a fuel bound, and a kernel-reduced equality
    for [run_fuel].  The conclusion is CompCert's actual function-call
    semantics for that same function. *)
Corollary run_fuel_funcall2:
  forall fuel ge f m le' m' v ty vres,
  fn_params f = nil ->
  fn_vars f = nil ->
  fn_return f <> Tvoid ->
  run_fuel fuel (genv_cenv ge) m (fn_body f)
    (create_undef_temps (fn_temps f))
    = Some (le', (m', Out_return (Some (v, ty)))) ->
  sem_cast v ty (fn_return f) m' = Some vres ->
  ClightBigstep.eval_funcall function_entry2 ge m (Internal f) nil E0 m' vres.
Proof.
  intros fuel ge f m le' m' v ty vres P V R RUN CAST.
  eapply eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m').
  - (* function_entry2 *)
    constructor.
    + rewrite V; constructor.
    + rewrite P; constructor.
    + rewrite P; red; simpl; tauto.
    + rewrite V; constructor.
    + rewrite P; reflexivity.
  - (* body *)
    eapply run_fuel_sound; eauto.
  - (* outcome_result_value: fn_return <> Tvoid /\ return-type cast *)
    simpl; auto.
  - (* free_list of an empty env *)
    reflexivity.
Qed.

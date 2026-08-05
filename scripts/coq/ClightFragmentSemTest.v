(* Regression for the generic rolled-control-flow theorem.

   The body below is an actual Clight function: initialize two temporaries,
   execute a one-iteration while loop, and return 2.  The closed evaluator
   equality is discharged by Coq computation; [run_fuel_funcall2] turns it
   into CompCert's function-call semantics. *)

From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightFragmentSem.

Local Open Scope positive_scope.

Definition _i : ident := 1.
Definition _out : ident := 2.

Definition rolled_body : statement :=
  Ssequence
    (Sset _i (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Sset _out (Econst_long (Int64.repr 0) tulong))
      (Ssequence
        (Sloop
          (Ssequence
            (Sifthenelse
              (Ebinop Olt (Etempvar _i tulong)
                (Econst_long (Int64.repr 1) tulong) tint)
              Sskip Sbreak)
            (Ssequence
              (Sset _out
                (Ebinop Oadd (Etempvar _out tulong)
                  (Econst_long (Int64.repr 2) tulong) tulong))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tulong)
                  (Econst_long (Int64.repr 1) tulong) tulong))))
          Sskip)
        (Sreturn (Some (Etempvar _out tulong))))).

Definition rolled_function : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := (_i, tulong) :: (_out, tulong) :: nil;
  fn_body := rolled_body
|}.

Definition rolled_expected : val := Vlong (Int64.repr 2).

Definition rolled_ge : genv := {|
  genv_genv := @Genv.empty_genv fundef type nil;
  genv_cenv := PTree.empty composite
|}.

Lemma rolled_run : exists le',
  run_fuel 8 (genv_cenv rolled_ge) Mem.empty (fn_body rolled_function)
    (create_undef_temps (fn_temps rolled_function)) =
  Some (le', (Mem.empty, Out_return (Some (rolled_expected, tulong)))).
Proof.
  eexists. vm_compute. reflexivity.
Qed.

Theorem rolled_bigstep : forall fe, exists le',
  ClightBigstep.exec_stmt fe rolled_ge empty_env
    (create_undef_temps (fn_temps rolled_function)) Mem.empty
    (fn_body rolled_function) E0 le' Mem.empty
    (Out_return (Some (rolled_expected, tulong))).
Proof.
  intros fe.
  destruct rolled_run as [le' RUN].
  exists le'.
  eapply run_fuel_sound with (fuel := 8%nat).
  exact RUN.
Qed.

Theorem rolled_funcall :
  ClightBigstep.eval_funcall function_entry2 rolled_ge Mem.empty
    (Internal rolled_function) nil E0 Mem.empty rolled_expected.
Proof.
  destruct rolled_run as [le' RUN].
  eapply run_fuel_funcall2 with
    (fuel := 8%nat) (le' := le') (v := rolled_expected) (ty := tulong).
  - reflexivity.
  - reflexivity.
  - discriminate.
  - exact RUN.
  - reflexivity.
Qed.

(* Exact emitter-shaped Clight compiler for the rolled AProgram fragment.

   The source language is the scalar certificate DSL plus typed loads and
   stores through one uint64_t array parameter.  The compiler deliberately
   reproduces the syntax printed by AProgram.emitRolled: scratch, ordinary
   registers, a separate loop counter, one base-pointer parameter, and one
   Swhile.  Its syntax size is independent of the loop count. *)

From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Values Events Memory Globalenvs.
From compcert Require Import AST Ctypes Cop Clight ClightBigstep Clightdefs.
Require Import Direct.ClightDSLCompiler Direct.ClightRolledCompiler.
Require Import Direct.ClightEmitterCompiler Direct.ClightFlatSem.

Import ListNotations.
Local Open Scope Z_scope.

Inductive adinstr : Type :=
  | ADscalar (i: dinstr)
  | ADload (dst index_reg: nat)
  | ADstore (index_reg source_reg: nat).

Record adsl_program : Type := {
  ap_reg_count: nat;
  ap_array_len: Z;
  ap_loop_count: nat;
  ap_init: list adinstr;
  ap_body: list adinstr;
  ap_epilogue: list adinstr;
  ap_output: nat
}.

Record adsl_state : Type := {
  ads_temps: temp_env;
  ads_cells: flat_cells
}.

Definition array_byte_offset (index: int64) : Z :=
  8 * Int64.unsigned index.

Definition array_index_ok (array_len: Z) (index: int64) : bool :=
  (Int64.unsigned index <? array_len)%Z.

Definition eval_adinstr (array_len: Z) (idx: nat)
    (st: adsl_state) (i: adinstr) : option adsl_state :=
  match i with
  | ADscalar scalar =>
      match eval_instr idx st.(ads_temps) scalar with
      | Some temps => Some {| ads_temps := temps;
                              ads_cells := st.(ads_cells) |}
      | None => None
      end
  | ADload dst index_reg =>
      match PTree.get (reg_ident index_reg) st.(ads_temps) with
      | Some (Vlong index) =>
          if array_index_ok array_len index then
            Some {| ads_temps := PTree.set (reg_ident dst)
                      (Vlong (flat_load st.(ads_cells)
                        (array_byte_offset index))) st.(ads_temps);
                    ads_cells := st.(ads_cells) |}
          else None
      | _ => None
      end
  | ADstore index_reg source_reg =>
      match PTree.get (reg_ident index_reg) st.(ads_temps),
            PTree.get (reg_ident source_reg) st.(ads_temps) with
      | Some (Vlong index), Some (Vlong value) =>
          if array_index_ok array_len index then
            Some {| ads_temps := st.(ads_temps);
                    ads_cells := flat_store st.(ads_cells)
                      (array_byte_offset index) value |}
          else None
      | _, _ => None
      end
  end.

Fixpoint eval_adinstrs (array_len: Z) (idx: nat) (is: list adinstr)
    (st: adsl_state) : option adsl_state :=
  match is with
  | [] => Some st
  | i :: rest =>
      match eval_adinstr array_len idx st i with
      | Some st' => eval_adinstrs array_len idx rest st'
      | None => None
      end
  end.

Fixpoint eval_aloop (array_len: Z) (idx count: nat)
    (body: list adinstr) (st: adsl_state) : option adsl_state :=
  match count with
  | O => Some st
  | S count' =>
      match eval_adinstrs array_len idx body st with
      | Some st' => eval_aloop array_len (S idx) count' body st'
      | None => None
      end
  end.

Definition adsl_initial_state (p: adsl_program) : adsl_state := {|
  ads_temps := create_undef_temps (temp_decls (ap_reg_count p));
  ads_cells := PTree.empty int64
|}.

Definition adsl_preamble (n: nat) : list adinstr :=
  map ADscalar (preamble n).

Definition adsl_denote (p: adsl_program) : option int64 :=
  match eval_adinstrs (ap_array_len p) 0
      (adsl_preamble (ap_reg_count p) ++ ap_init p)
      (adsl_initial_state p) with
  | Some st1 =>
      match eval_aloop (ap_array_len p) 0 (ap_loop_count p)
          (ap_body p) st1 with
      | Some st2 =>
          match eval_adinstrs (ap_array_len p) 0 (ap_epilogue p) st2 with
          | Some st3 =>
              match PTree.get (reg_ident (ap_output p)) st3.(ads_temps) with
              | Some (Vlong w) => Some w
              | _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition adinstr_wf (n: nat) (i: adinstr) : Prop :=
  match i with
  | ADscalar scalar => dinstr_wf n scalar
  | ADload dst index_reg => (dst < n)%nat /\ (index_reg < n)%nat
  | ADstore index_reg source_reg =>
      (index_reg < n)%nat /\ (source_reg < n)%nat
  end.

Record adsl_wf (p: adsl_program) : Prop := {
  ap_output_wf: (ap_output p < ap_reg_count p)%nat;
  ap_init_wf: Forall (adinstr_wf (ap_reg_count p)) (ap_init p);
  ap_body_wf: Forall (adinstr_wf (ap_reg_count p)) (ap_body p);
  ap_epilogue_wf: Forall (adinstr_wf (ap_reg_count p)) (ap_epilogue p);
  ap_loop_fits: Z.of_nat (ap_loop_count p) < Int64.modulus;
  ap_array_nonnegative: 0 <= ap_array_len p;
  ap_array_fits: 8 * ap_array_len p <= Ptrofs.modulus
}.

(* The data inspected by syntax generation.  Counts and the array length are
   kept out so exact AST conversion never normalizes a large unary nat. *)
Record array_emitter_source : Type := {
  aes_reg_count: nat;
  aes_init: list adinstr;
  aes_body: list adinstr;
  aes_epilogue: list adinstr;
  aes_output: nat
}.

Record array_emitter_source_matches
    (s: array_emitter_source) (p: adsl_program) : Prop := {
  aesm_reg_count: aes_reg_count s = ap_reg_count p;
  aesm_init: aes_init s = ap_init p;
  aesm_body: aes_body s = ap_body p;
  aesm_epilogue: aes_epilogue s = ap_epilogue p;
  aesm_output: aes_output s = ap_output p
}.

Record array_emitter_layout : Type := {
  ael_scalar: emitter_layout;
  ael_base: ident
}.

Definition array_emitter_layout_wf (l: array_emitter_layout) (n: nat) : Prop :=
  emitter_layout_wf (ael_scalar l) n /\
  ael_base l <> el_scratch (ael_scalar l) /\
  ael_base l <> el_counter (ael_scalar l) /\
  ~ In (ael_base l) (el_regs (ael_scalar l)).

Definition array_base_type : type := tptr tulong.

Definition array_address (l: array_emitter_layout) (index_reg: nat) : expr :=
  Ebinop Oadd
    (Etempvar (ael_base l) array_base_type)
    (Etempvar (el_reg (ael_scalar l) index_reg) tulong)
    array_base_type.

Definition array_emitter_instr (l: array_emitter_layout) (idx: expr)
    (i: adinstr) : list statement :=
  match i with
  | ADscalar scalar => emitter_instr (ael_scalar l) idx scalar
  | ADload dst index_reg =>
      [Sset (el_reg (ael_scalar l) dst)
        (Ederef (array_address l index_reg) tulong)]
  | ADstore index_reg source_reg =>
      [Sassign (Ederef (array_address l index_reg) tulong)
        (Etempvar (el_reg (ael_scalar l) source_reg) tulong)]
  end.

Fixpoint array_emitter_instrs (l: array_emitter_layout) (idx: expr)
    (is: list adinstr) : list statement :=
  match is with
  | [] => []
  | i :: rest =>
      array_emitter_instr l idx i ++ array_emitter_instrs l idx rest
  end.

Definition array_emitter_loop_body (l: array_emitter_layout)
    (body: list adinstr) : statement :=
  emitter_sequence
    (array_emitter_instrs l
      (Etempvar (el_counter (ael_scalar l)) tulong) body ++
     [emitter_increment (ael_scalar l)]).

Definition array_emitter_loop (l: array_emitter_layout) (limit: Z)
    (body: list adinstr) : statement :=
  Swhile (emitter_test (ael_scalar l) limit)
    (array_emitter_loop_body l body).

Definition array_emitter_preamble (l: array_emitter_layout) (n: nat)
    : list statement :=
  [emitter_scratch_zero (ael_scalar l)] ++
  emitter_instrs (ael_scalar l) (Econst_long Int64.zero tulong)
    (preamble n) ++
  [emitter_counter_zero (ael_scalar l)].

Definition array_emitter_body_statements (l: array_emitter_layout)
    (loop_limit: Z) (s: array_emitter_source) : list statement :=
  array_emitter_preamble l (aes_reg_count s) ++
  array_emitter_instrs l (Econst_long Int64.zero tulong) (aes_init s) ++
  [emitter_counter_zero (ael_scalar l)] ++
  [array_emitter_loop l loop_limit (aes_body s)] ++
  array_emitter_instrs l (Econst_long Int64.zero tulong) (aes_epilogue s) ++
  [Sreturn (Some
    (Etempvar (el_reg (ael_scalar l) (aes_output s)) tulong))].

Definition compile_array_emitted_rolled_body (l: array_emitter_layout)
    (loop_limit: Z) (s: array_emitter_source) : statement :=
  emitter_sequence (array_emitter_body_statements l loop_limit s).

Definition compile_array_emitted_rolled_program
    (l: array_emitter_layout) (loop_limit: Z)
    (s: array_emitter_source) : function := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := [(ael_base l, array_base_type)];
  fn_vars := [];
  fn_temps := emitter_temp_decls (ael_scalar l);
  fn_body := compile_array_emitted_rolled_body l loop_limit s
|}.

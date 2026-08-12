import LeanCompCert.Ports.CDEMAbelMarkTelescope
import LeanCompCert.Ports.CDEMAbelOuterSchedule

/-! # Changing-index fidelity for the CDEM accumulation schedule

Only the first phase-selector instruction reads the emitted loop index.  Once
both indices are past the sieve prefix, that selector has the same value and
the rest of the body is index-free.  This file turns that observation into an
exact equality between the convenient fixed-index cell scheduler and the
literal changing-index execution used by the compiled program.
-/

namespace LeanCompCert.Ports.CDEMAbelIndexIndependence

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelMarkTelescope

def operandIndexFree : Operand → Bool
  | .reg _ | .lit _ => true
  | .idx => false

def instrIndexFree : Instr → Bool
  | .mov _ src => operandIndexFree src
  | .binop _ _ lhs rhs => operandIndexFree lhs && operandIndexFree rhs

def ainstrIndexFree : AInstr → Bool
  | .scalar i => instrIndexFree i
  | .load _ _ | .store _ _ => true

theorem denoteOperand_indexFree (i j : Nat) (r : RegState)
    (op : Operand) (h : operandIndexFree op = true) :
    denoteOperand i r op = denoteOperand j r op := by
  cases op <;> simp_all [operandIndexFree, denoteOperand]

theorem astep_indexFree (i j : Nat) (st : AState) (instr : AInstr)
    (h : ainstrIndexFree instr = true) :
    astep i st instr = astep j st instr := by
  cases instr with
  | scalar instr =>
      cases instr with
      | mov dest src =>
          simp only [ainstrIndexFree, instrIndexFree] at h
          simp only [astep, LeanCompCert.Verified.InstrBlock.sdest,
            LeanCompCert.Verified.InstrBlock.sval]
          rw [denoteOperand_indexFree i j st.regs src h]
      | binop dest op lhs rhs =>
          simp only [ainstrIndexFree, instrIndexFree, Bool.and_eq_true] at h
          rcases h with ⟨hlhs, hrhs⟩
          simp only [astep, LeanCompCert.Verified.InstrBlock.sdest,
            LeanCompCert.Verified.InstrBlock.sval]
          rw [denoteOperand_indexFree i j st.regs lhs hlhs,
            denoteOperand_indexFree i j st.regs rhs hrhs]
  | load dest address => rfl
  | store address src => rfl

theorem arun_indexFree (i j : Nat) : ∀ (block : List AInstr) (st : AState),
    block.all ainstrIndexFree = true →
    arun i st block = arun j st block := by
  intro block
  induction block with
  | nil => intro st _; rfl
  | cons instr rest ih =>
      intro st h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, arun_cons, astep_indexFree i j st instr h.1]
      exact ih _ h.2

def accumulationSuffix (c : Cfg) : List AInstr :=
  c.sieveBody ++ c.markBody ++ c.accBody ++ c.tailBody

set_option maxRecDepth 10000 in
theorem accumulationSuffix_indexFree (c : Cfg) :
    (accumulationSuffix c).all ainstrIndexFree = true := by
  rfl

theorem selectors_index_independent (c : Cfg) (i j : Nat) (st : AState)
    (hiM : i < M) (hjM : j < M) (hsieveM : c.sieveLen < M)
    (hi : c.sieveLen ≤ i) (hj : c.sieveLen ≤ j) :
    arun i st c.selectors = arun j st c.selectors := by
  have hiMod : i % M = i := Nat.mod_eq_of_lt hiM
  have hjMod : j % M = j := Nat.mod_eq_of_lt hjM
  have hsieveMod : c.sieveLen % M = c.sieveLen :=
    Nat.mod_eq_of_lt hsieveM
  have hni : ¬i < c.sieveLen := Nat.not_lt.mpr hi
  have hnj : ¬j < c.sieveLen := Nat.not_lt.mpr hj
  simp [Cfg.selectors, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hiMod, hjMod, hsieveMod, hni, hnj]

theorem body_index_independent (c : Cfg) (i j : Nat) (st : AState)
    (hiM : i < M) (hjM : j < M) (hsieveM : c.sieveLen < M)
    (hi : c.sieveLen ≤ i) (hj : c.sieveLen ≤ j) :
    arun i st c.body = arun j st c.body := by
  have hbody : c.body = c.selectors ++ accumulationSuffix c := by
    simp [Cfg.body, accumulationSuffix, Cfg.accBody, List.append_assoc]
  rw [hbody, arun_append, arun_append]
  rw [selectors_index_independent c i j st hiM hjM hsieveM hi hj]
  exact arun_indexFree i j (accumulationSuffix c)
    (arun j st c.selectors) (accumulationSuffix_indexFree c)

theorem bodyIter_succ_seed (c : Cfg) (idx n : Nat) (st : AState) :
    bodyIter c idx (n + 1) st =
      bodyIter c idx n (arun idx st c.body) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change arun idx (bodyIter c idx (n + 1) st) c.body =
        arun idx (bodyIter c idx n (arun idx st c.body)) c.body
      rw [ih]

theorem bodyIterFrom_eq_bodyIter (c : Cfg) (start n : Nat) (st : AState)
    (hidxM : start + n < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ start) :
    bodyIterFrom c start n st = bodyIter c start n st := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change arun (start + n) (bodyIterFrom c start n st) c.body =
        arun start (bodyIter c start n st) c.body
      rw [ih (by omega)]
      exact body_index_independent c (start + n) start
        (bodyIter c start n st) (by omega) (by omega) hsieveM
        (by omega) hsieve

theorem bodyIterFrom_add (c : Cfg) (start left right : Nat) (st : AState) :
    bodyIterFrom c start (left + right) st =
      bodyIterFrom c (start + left) right
        (bodyIterFrom c start left st) := by
  induction right with
  | zero => simp [bodyIterFrom]
  | succ right ih =>
      change arun (start + (left + right))
          (bodyIterFrom c start (left + right) st) c.body =
        arun (start + left + right)
          (bodyIterFrom c (start + left) right
            (bodyIterFrom c start left st)) c.body
      rw [ih]
      congr 1
      omega

/-- A complete paper cell schedule is exactly `bsSteps + 1` consecutive
iterations of the emitted changing-index loop. -/
theorem bodySchedule_eq_bodyIterFrom (c : Cfg) (start middleCount : Nat)
    (st : AState) (hidxM : start + middleCount + 2 < M)
    (hsieveM : c.sieveLen < M) (hsieve : c.sieveLen ≤ start) :
    bodySchedule c start middleCount st =
      bodyIterFrom c start (middleCount + 2) st := by
  rw [bodyIterFrom_eq_bodyIter c start (middleCount + 2) st
    (by omega) hsieveM hsieve]
  change bodySchedule c start middleCount st =
    arun start (bodyIter c start (middleCount + 1) st) c.body
  rw [bodyIter_succ_seed]
  rfl

end LeanCompCert.Ports.CDEMAbelIndexIndependence

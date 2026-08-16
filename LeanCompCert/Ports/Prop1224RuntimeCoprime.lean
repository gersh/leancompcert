import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Runtime coprimality walk for Proposition 12.2.4

The shared table contains the smallest prime factor of each `r`.  Starting
from `m = r`, one fixed-shape round loads `spf(m)`, tests `q % spf(m)`, and
divides `m` by that factor.  Completed states (`m = 1`) are fixed points.
The enclosing checker uses a fixed round budget and increments its violation
counter unless the final `m` is exactly one, so truncation cannot be accepted.
-/

namespace LeanCompCert.Ports.Prop1224RuntimeCoprime

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def rQ : Nat := 0
def rM : Nat := 1
def rCop : Nat := 2
def rAddr : Nat := 3
def rP : Nat := 4
def rPZero : Nat := 5
def rPSafe : Nat := 6
def rActive : Nat := 7
def rRem : Nat := 8
def rNondiv : Nat := 9
def rKeep : Nat := 10
def rSelect : Nat := 11
def rQuot : Nat := 12
def rNext : Nat := 13
def regCount : Nat := 14

def round (spfBase : Nat) : List AInstr :=
  [ .scalar (.binop rAddr .add (.reg rM) (.lit spfBase))
  , .load rP rAddr
  , .scalar (.binop rPZero .eq (.reg rP) (.lit 0))
  , .scalar (.binop rPSafe .add (.reg rP) (.reg rPZero))
  , .scalar (.binop rActive .ne (.reg rM) (.lit 1))
  , .scalar (.binop rRem .urem (.reg rQ) (.reg rPSafe))
  , .scalar (.binop rNondiv .ne (.reg rRem) (.lit 0))
  , .scalar (.binop rKeep .sub (.lit 1) (.reg rActive))
  , .scalar (.binop rSelect .mul (.reg rActive) (.reg rNondiv))
  , .scalar (.binop rSelect .add (.reg rSelect) (.reg rKeep))
  , .scalar (.binop rCop .mul (.reg rCop) (.reg rSelect))
  , .scalar (.binop rQuot .udiv (.reg rM) (.reg rPSafe))
  , .scalar (.binop rNext .mul (.reg rActive) (.reg rQuot))
  , .scalar (.binop rKeep .mul (.reg rKeep) (.lit 1))
  , .scalar (.binop rM .add (.reg rNext) (.reg rKeep)) ]

def rounds (spfBase n : Nat) : List AInstr :=
  (List.replicate n (round spfBase)).flatten

def step (spf : Nat → Nat) (q : Nat) (pair : Nat × Nat) : Nat × Nat :=
  if pair.1 = 1 then pair
  else
    let p := spf pair.1
    (pair.1 / p, pair.2 * if q % p = 0 then 0 else 1)

def stateAfter (spf : Nat → Nat) (q : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, pair => pair
  | n + 1, pair => stateAfter spf q n (step spf q pair)

/-- One emitted table walk round is exactly the guarded source step.  The
table hypotheses make the physical load and both divisions defined; all word
bounds are explicit. -/
theorem round_run (spfBase len k q m cop : Nat) (spf : Nat → Nat) (s : AState)
    (hq : s.regs rQ = q) (hm : s.regs rM = m) (hcop : s.regs rCop = cop)
    (harr : s.arr (spfBase + m) = spf m)
    (haddr : spfBase + m < len) (haddrM : spfBase + m < M)
    (hp : 0 < spf m) (hpM : spf m < M)
    (hqM : q < M) (hmM : m < M) (hcop1 : cop ≤ 1) :
    let out := arun k s (round spfBase)
    out.regs rM = (step spf q (m, cop)).1 ∧
      out.regs rCop = (step spf q (m, cop)).2 ∧ out.arr = s.arr := by
  have hqmodM : q % spf m < M :=
    Nat.lt_trans (Nat.mod_lt q hp) hpM
  have hdivM : m / spf m < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self m _) hmM
  have hcopM : cop < M := Nat.lt_of_le_of_lt hcop1 (by decide)
  have hselM : cop * (if q % spf m = 0 then 0 else 1) < M := by
    split <;> simp_all
  have hq' : s.regs 0 = q := by simpa [rQ] using hq
  have hm' : s.regs 1 = m := by simpa [rM] using hm
  have hcop' : s.regs 2 = cop := by simpa [rCop] using hcop
  have haddrMod : (spfBase + m) % M = spfBase + m :=
    Nat.mod_eq_of_lt haddrM
  have haddrMod' : (m + spfBase) % M = m + spfBase := by
    simpa [Nat.add_comm] using haddrMod
  have haddr' : m + spfBase < len := by simpa [Nat.add_comm] using haddr
  have harr' : s.arr (m + spfBase) = spf m := by
    simpa [Nat.add_comm] using harr
  have hmMod : m % M = m := Nat.mod_eq_of_lt hmM
  have honeM : (1 : Nat) < M := by decide
  have hpne : spf m ≠ 0 := Nat.ne_of_gt hp
  have hMsub1 : 1 + (M - 1) = M := by omega
  by_cases hm1 : m = 1
  · simp [round, step, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rQ, rM, rCop, rAddr, rP, rPZero, rPSafe, rActive,
      rRem, rNondiv, rKeep, rSelect, rQuot, rNext,
      hq', hm', hcop', harr', haddr', haddrMod', hmMod, hpne, hcopM, hm1,
      hMsub1, Nat.mod_eq_of_lt honeM,
      Nat.mod_eq_of_lt hpM, Nat.mod_eq_of_lt hqM,
      Nat.mod_eq_of_lt hqmodM, Nat.mod_eq_of_lt hdivM]
    exact Nat.mod_eq_of_lt hcopM
  · simp [round, step, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rQ, rM, rCop, rAddr, rP, rPZero, rPSafe, rActive,
      rRem, rNondiv, rKeep, rSelect, rQuot, rNext,
      hq', hm', hcop', harr', haddr', haddrMod', hmMod, hpne, hp, hpM, hqM,
      hmM, hcopM, honeM, hm1, hMsub1, Nat.mod_eq_of_lt honeM,
      Nat.mod_eq_of_lt hpM, Nat.mod_eq_of_lt hqM,
      Nat.mod_eq_of_lt hqmodM, Nat.mod_eq_of_lt hdivM,
      Nat.mod_eq_of_lt hselM]

theorem step_completed (spf : Nat → Nat) (q cop : Nat) :
    step spf q (1, cop) = (1, cop) := by simp [step]

theorem stateAfter_completed (spf : Nat → Nat) (q cop n : Nat) :
    stateAfter spf q n (1, cop) = (1, cop) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [stateAfter, step_completed] using ih

#print axioms round_run
#print axioms stateAfter_completed

end LeanCompCert.Ports.Prop1224RuntimeCoprime

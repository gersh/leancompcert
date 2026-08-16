import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Dynamic compiled gcd for Proposition 12.2.4 cell rows

Compact row records carry `q` at runtime, so the cell consumer cannot emit a
literal prime-divisor list per row.  This fixed-round Euclidean block computes
`gcd(q,r)` dynamically.  A zero divisor is replaced by one before `urem`, and
completed states are framed.  The consumer separately requires the final
second limb to be zero; therefore the fixed budget cannot silently truncate
Euclid.
-/

namespace LeanCompCert.Ports.Prop1224DynamicGCD

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def rA : Nat := 0
def rB : Nat := 1
def rSafe : Nat := 2
def rZero : Nat := 3
def rActive : Nat := 4
def rRem : Nat := 5
def rKeep : Nat := 6
def rTake : Nat := 7
def regCount : Nat := 8

def round : List AInstr :=
  [ .scalar (.binop rZero .eq (.reg rB) (.lit 0))
  , .scalar (.binop rSafe .add (.reg rB) (.reg rZero))
  , .scalar (.binop rRem .urem (.reg rA) (.reg rSafe))
  , .scalar (.binop rActive .sub (.lit 1) (.reg rZero))
  , .scalar (.binop rKeep .mul (.reg rA) (.reg rZero))
  , .scalar (.binop rTake .mul (.reg rB) (.reg rActive))
  , .scalar (.binop rA .add (.reg rKeep) (.reg rTake))
  , .scalar (.binop rB .mul (.reg rRem) (.reg rActive)) ]

def rounds (n : Nat) : List AInstr := (List.replicate n round).flatten

def step (pair : Nat × Nat) : Nat × Nat :=
  if pair.2 = 0 then pair else (pair.2, pair.1 % pair.2)

def stateAfter : Nat → Nat × Nat → Nat × Nat
  | 0, pair => pair
  | n + 1, pair => stateAfter n (step pair)

theorem round_run (k a b : Nat) (s : AState)
    (ha : s.regs rA = a) (hb : s.regs rB = b)
    (haM : a < M) (hbM : b < M) :
    let out := arun k s round
    out.regs rA = (step (a, b)).1 ∧
      out.regs rB = (step (a, b)).2 := by
  by_cases hzero : b = 0
  · have ha' : s.regs 0 = a := by simpa [rA] using ha
    have hb' : s.regs 1 = 0 := by simpa [rB, hzero] using hb
    have honeM : 1 < M := by decide
    simp [round, step, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rA, rB, rSafe, rZero, rActive, rRem, rKeep, rTake,
      ha', hb', hzero, Nat.mod_one, Nat.mod_eq_of_lt haM,
      Nat.mod_eq_of_lt honeM]
  · have hbPos : 0 < b := Nat.pos_of_ne_zero hzero
    have hremM : a % b < M := Nat.lt_trans (Nat.mod_lt a hbPos) hbM
    have honeM : 1 < M := by decide
    have ha' : s.regs 0 = a := by simpa [rA] using ha
    have hb' : s.regs 1 = b := by simpa [rB] using hb
    simp [round, step, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rA, rB, rSafe, rZero, rActive, rRem, rKeep, rTake,
      ha', hb', hzero, Nat.mod_eq_of_lt haM, Nat.mod_eq_of_lt hbM,
      Nat.mod_eq_of_lt hremM, Nat.mod_eq_of_lt honeM]

theorem rounds_run (n k a b : Nat) (s : AState)
    (ha : s.regs rA = a) (hb : s.regs rB = b)
    (haM : a < M) (hbM : b < M) :
    let out := arun k s (rounds n)
    out.regs rA = (stateAfter n (a, b)).1 ∧
      out.regs rB = (stateAfter n (a, b)).2 := by
  induction n generalizing s a b with
  | zero => simpa [rounds, stateAfter, arun] using And.intro ha hb
  | succ n ih =>
      rw [rounds, List.replicate_succ, List.flatten_cons, arun_append]
      have hround := round_run k a b s ha hb haM hbM
      let pair := step (a, b)
      have hpairA : pair.1 < M := by
        by_cases hzero : b = 0
        · simpa [pair, step, hzero] using haM
        · simpa [pair, step, hzero] using hbM
      have hpairB : pair.2 < M := by
        by_cases hzero : b = 0
        · simpa [pair, step, hzero] using hbM
        · exact Nat.lt_trans
            (by simpa [pair, step, hzero] using Nat.mod_lt a (Nat.pos_of_ne_zero hzero))
            hbM
      have htail := ih pair.1 pair.2 (arun k s round)
        hround.1 hround.2 hpairA hpairB
      simpa [rounds, stateAfter, pair, Prod.eta] using htail

theorem step_gcd (a b : Nat) :
    Nat.gcd (step (a, b)).1 (step (a, b)).2 = Nat.gcd a b := by
  by_cases hzero : b = 0
  · simp [step, hzero]
  · rw [step]
    simp only [hzero, ↓reduceIte]
    rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm b a]

theorem stateAfter_gcd_invariant (n a b : Nat) :
    Nat.gcd (stateAfter n (a, b)).1 (stateAfter n (a, b)).2 = Nat.gcd a b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
      rw [stateAfter, ih, step_gcd]

/-- Once the compiled completion guard observes zero, the first limb is the
mathematical gcd.  No theorem about a fixed worst-case iteration count is
needed for soundness. -/
theorem stateAfter_gcd (n a b : Nat)
    (hdone : (stateAfter n (a, b)).2 = 0) :
    (stateAfter n (a, b)).1 = Nat.gcd a b := by
  calc
    (stateAfter n (a, b)).1 =
        Nat.gcd (stateAfter n (a, b)).1 0 := (Nat.gcd_zero_right _).symm
    _ = Nat.gcd (stateAfter n (a, b)).1 (stateAfter n (a, b)).2 := by rw [hdone]
    _ = Nat.gcd a b := stateAfter_gcd_invariant n a b

#print axioms round_run
#print axioms rounds_run
#print axioms stateAfter_gcd

end LeanCompCert.Ports.Prop1224DynamicGCD

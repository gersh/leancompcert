import LeanCompCert.Ports.Prop1224CellAccBodySemantics
import LeanCompCert.Ports.Prop1224CellGuardedSemantics

/-!
# Modulo-first accumulation semantics for Proposition 12.2.4

The historical exact-step theorem assumes in advance that the `G_q`
accumulator does not wrap.  The signed guarded program checks that fact at
runtime.  These lemmas first prove the literal modulo-`2^64` denotation, then
recover ordinary natural addition from the guard's causal no-decrease fact.
Thus future receipts certify the expensive range fact instead of asking Lean
to compute a production prefix.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.Prop1224Margin (C gqTerm)

/-- The literal add suffix always denotes modular addition; no source
no-wrap premise is needed for this statement. -/
theorem accAddSuffix_run_mod (k term take g : Nat) (s : AState)
    (hTerm : s.regs 103 = term) (hTake : s.regs 100 = take)
    (hAcc : s.regs 12 = 1) (hG : s.regs rG = g)
    (hProductM : term * take < M) :
    let out := arun k s accAddSuffix
    out.regs rG = (g + term * take) % M ∧ out.arr = s.arr := by
  have hG180 : s.regs 180 = g := by simpa [rG] using hG
  simp [accAddSuffix, arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    rG, hTerm, hTake, hAcc, hG180, Nat.mod_eq_of_lt hProductM]

theorem accComputeSuffix_run_mod (k phi sqbit cop g : Nat) (s : AState)
    (hPhi : s.regs 98 = phi) (hSq : s.regs 99 = sqbit)
    (hCop : s.regs 81 = cop) (hAcc : s.regs 12 = 1)
    (hG : s.regs rG = g) (hPhiPos : 0 < phi)
    (hSumM : 2 ^ C + phi < M) (hTermM : gqTerm phi < M)
    (hbit : sqbit ≤ 1) (hcopbit : cop ≤ 1) :
    let inc := gqTerm phi * (sqbit * cop)
    let out := arun k s accComputeSuffix
    out.regs rG = (g + inc) % M ∧ out.arr = s.arr := by
  have hIncLe : gqTerm phi * (sqbit * cop) ≤ gqTerm phi := by
    have hsqcases : sqbit = 0 ∨ sqbit = 1 := by omega
    have hcopcases : cop = 0 ∨ cop = 1 := by omega
    rcases hsqcases with rfl | rfl <;>
      rcases hcopcases with rfl | rfl <;> simp
  have hIncM : gqTerm phi * (sqbit * cop) < M :=
    Nat.lt_of_le_of_lt hIncLe hTermM
  let gated := arun k s accGateSuffix
  have hg := accGateSuffix_run k sqbit cop s hSq hCop hbit hcopbit
  dsimp only at hg
  let ceiled := arun k gated accCeilSuffix
  have hPhi' : gated.regs 98 = phi :=
    (arun_frame k 98 accGateSuffix (by rfl) s).trans hPhi
  have hc := accCeilSuffix_run k phi gated hPhi' hPhiPos hSumM hTermM
  dsimp only at hc
  have hTake' : ceiled.regs 100 = sqbit * cop :=
    (arun_frame k 100 accCeilSuffix (by rfl) gated).trans hg.1
  have hAcc' : ceiled.regs 12 = 1 :=
    (arun_frame k 12 accCeilSuffix (by rfl) gated).trans
      ((arun_frame k 12 accGateSuffix (by rfl) s).trans hAcc)
  have hG' : ceiled.regs rG = g :=
    (arun_frame k rG accCeilSuffix (by rfl) gated).trans
      ((arun_frame k rG accGateSuffix (by rfl) s).trans hG)
  have ha := accAddSuffix_run_mod k (gqTerm phi) (sqbit * cop) g
    ceiled hc.1 hTake' hAcc' hG' hIncM
  dsimp only at ha
  rw [accComputeSuffix, arun_append, arun_append]
  exact ha

theorem accSuffix_run_mod (c : CellCfg) (k i phi sqbit cop g : Nat)
    (s : AState)
    (hI : s.regs 86 = i) (hPhi : s.regs 98 = phi)
    (hSq : s.regs 99 = sqbit) (hCop : s.regs 81 = cop)
    (hAcc : s.regs 12 = 1) (hG : s.regs rG = g)
    (hOne : s.regs rOne = 1) (hZero : s.regs rZero = 0)
    (hi : i < c.segLen) (hIndexM : i + 3 * c.segLen < M)
    (hPhiPos : 0 < phi) (hSumM : 2 ^ C + phi < M)
    (hTermM : gqTerm phi < M)
    (hbit : sqbit ≤ 1) (hcopbit : cop ≤ 1) :
    let inc := gqTerm phi * (sqbit * cop)
    let value := (g + inc) % M
    let out := arun k s (accSuffix c)
    out.regs rG = value ∧ out.arr i = 1 ∧
      out.arr (i + c.segLen) = 1 ∧
      out.arr (i + 2 * c.segLen) = 0 ∧
      out.arr (i + 3 * c.segLen) = value := by
  let inc := gqTerm phi * (sqbit * cop)
  let value := (g + inc) % M
  let computed := arun k s accComputeSuffix
  have hc := accComputeSuffix_run_mod k phi sqbit cop g s hPhi hSq hCop
    hAcc hG hPhiPos hSumM hTermM hbit hcopbit
  dsimp only at hc
  have hI' : computed.regs 86 = i :=
    (arun_frame k 86 accComputeSuffix (by rfl) s).trans hI
  have hAcc' : computed.regs 12 = 1 :=
    (arun_frame k 12 accComputeSuffix (by rfl) s).trans hAcc
  have hOne' : computed.regs rOne = 1 :=
    (arun_frame k rOne accComputeSuffix (by rfl) s).trans hOne
  have hZero' : computed.regs rZero = 0 :=
    (arun_frame k rZero accComputeSuffix (by rfl) s).trans hZero
  have hvalueM : value < M := Nat.mod_lt _ (by decide)
  have hr := accResetSuffix_run c k i value computed hI' hAcc' hc.1
    hOne' hZero' hi hIndexM hvalueM
  dsimp only at hr
  rw [accSuffix, arun_append]
  exact hr

/-- Complete literal accumulation body with only the genuine word guards:
the accumulator result and published fourth-plane word are the modular source
increment. -/
theorem accBody_run_mod (c : CellCfg) (k i w radical phiSmall sqf phi g : Nat)
    (s : AState)
    (hR : s.regs rR = c.markSteps + i) (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w)
    (hProd : s.arr i = radical)
    (hPhi : s.arr (i + c.segLen) = phiSmall)
    (hSqf : s.arr (i + 2 * c.segLen) = sqf)
    (hG : s.regs rG = g) (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0)
    (hi : i < c.segLen) (hr : w + i < M)
    (hIndexM : i + 3 * c.segLen < M)
    (hT : c.markSteps < M) (hTi : c.markSteps + i < M)
    (hRadPos : 0 < radical) (hRadM : radical < M)
    (hRadDvd : radical ∣ w + i) (hRadLe : radical ≤ w + i)
    (hPhiSmallM : phiSmall < M) (hPhiPos : 0 < phi)
    (hPhiM : phi < M)
    (hPhiEq : phi = phiSmall *
      (if radical = w + i then 1 else (w + i) / radical - 1))
    (hPrimes : ∀ p ∈ c.qPrimes, 0 < p ∧ p < M)
    (hSumM : 2 ^ C + phi < M) (hTermM : gqTerm phi < M) :
    let take := (if sqf = 0 then 1 else 0) *
      coprimeIndicator c.qPrimes (w + i)
    let inc := gqTerm phi * take
    let value := (g + inc) % M
    let out := arun k s c.accBody
    out.regs rG = value ∧ out.arr i = 1 ∧
      out.arr (i + c.segLen) = 1 ∧
      out.arr (i + 2 * c.segLen) = 0 ∧
      out.arr (i + 3 * c.segLen) = value := by
  let pref := arun k s (accPrefix c)
  have hp := accPrefix_run c k i w radical phiSmall sqf phi s hR hAcc hW
    hProd hPhi hSqf hi hr hIndexM hT hTi hRadPos hRadM hRadDvd hRadLe
      hPhiSmallM hPhiM hPhiEq
  dsimp only at hp
  have hpAcc : pref.regs 12 = 1 :=
    (arun_frame k 12 (accPrefix c) (by rfl) s).trans hAcc
  have hpG : pref.regs rG = g :=
    (arun_frame k rG (accPrefix c) (by rfl) s).trans hG
  have hpOne : pref.regs rOne = 1 :=
    (arun_frame k rOne (accPrefix c) (by rfl) s).trans hOne
  have hpZero : pref.regs rZero = 0 :=
    (arun_frame k rZero (accPrefix c) (by rfl) s).trans hZero
  let copied := arun k pref (coprimeBody c.qPrimes)
  have hc := coprimeBody_run c.qPrimes k (w + i) pref hp.2.1
    hp.2.2.2.2.1 hPrimes
  dsimp only at hc
  have hcI : copied.regs 86 = i :=
    (coprimeBody_reg_frame c.qPrimes 86 k pref (by decide) (by decide)
      (by decide)).trans hp.1
  have hcPhi : copied.regs 98 = phi :=
    (coprimeBody_reg_frame c.qPrimes 98 k pref (by decide) (by decide)
      (by decide)).trans hp.2.2.1
  have hcSq : copied.regs 99 = (if sqf = 0 then 1 else 0) :=
    (coprimeBody_reg_frame c.qPrimes 99 k pref (by decide) (by decide)
      (by decide)).trans hp.2.2.2.1
  have hcAcc : copied.regs 12 = 1 :=
    (coprimeBody_reg_frame c.qPrimes 12 k pref (by decide) (by decide)
      (by decide)).trans hpAcc
  have hcG : copied.regs rG = g :=
    (coprimeBody_reg_frame c.qPrimes rG k pref (by decide) (by decide)
      (by decide)).trans hpG
  have hcOne : copied.regs rOne = 1 :=
    (coprimeBody_reg_frame c.qPrimes rOne k pref (by decide) (by decide)
      (by decide)).trans hpOne
  have hcZero : copied.regs rZero = 0 :=
    (coprimeBody_reg_frame c.qPrimes rZero k pref (by decide) (by decide)
      (by decide)).trans hpZero
  have hs := accSuffix_run_mod c k i phi (if sqf = 0 then 1 else 0)
    (coprimeIndicator c.qPrimes (w + i)) g copied hcI hcPhi hcSq hc.1
    hcAcc hcG hcOne hcZero hi hIndexM hPhiPos hSumM hTermM
    (by split <;> omega) (coprimeIndicator_le_one _ _)
  dsimp only at hs
  rw [accBody_eq, arun_append, arun_append]
  exact hs

/-- A causal no-decrease result from the guarded checker converts the raw
modular denotation into exact natural addition. -/
theorem accBody_run_exact_of_no_decrease
    (c : CellCfg) (k i w radical phiSmall sqf phi g : Nat) (s : AState)
    (hR : s.regs rR = c.markSteps + i) (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w) (hProd : s.arr i = radical)
    (hPhi : s.arr (i + c.segLen) = phiSmall)
    (hSqf : s.arr (i + 2 * c.segLen) = sqf)
    (hG : s.regs rG = g) (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0) (hi : i < c.segLen)
    (hr : w + i < M) (hIndexM : i + 3 * c.segLen < M)
    (hT : c.markSteps < M) (hTi : c.markSteps + i < M)
    (hRadPos : 0 < radical) (hRadM : radical < M)
    (hRadDvd : radical ∣ w + i) (hRadLe : radical ≤ w + i)
    (hPhiSmallM : phiSmall < M) (hPhiPos : 0 < phi)
    (hPhiM : phi < M)
    (hPhiEq : phi = phiSmall *
      (if radical = w + i then 1 else (w + i) / radical - 1))
    (hPrimes : ∀ p ∈ c.qPrimes, 0 < p ∧ p < M)
    (hSumM : 2 ^ C + phi < M) (hTermM : gqTerm phi < M)
    (hGword : g < M)
    (hNoDecrease : g ≤ (arun k s c.accBody).regs rG) :
    let inc := cellMarkedStep c.qPrimes (w + i) phi sqf
    let out := arun k s c.accBody
    g + inc < M ∧ out.regs rG = g + inc ∧
      out.arr i = 1 ∧ out.arr (i + c.segLen) = 1 ∧
      out.arr (i + 2 * c.segLen) = 0 ∧
      out.arr (i + 3 * c.segLen) = g + inc := by
  let take := (if sqf = 0 then 1 else 0) *
    coprimeIndicator c.qPrimes (w + i)
  let inc := gqTerm phi * take
  have htake : take ≤ 1 := by
    dsimp only [take]
    have hcop := coprimeIndicator_le_one c.qPrimes (w + i)
    split <;> omega
  have hinc : inc ≤ gqTerm phi := by
    dsimp only [inc]
    have htakeCases : take = 0 ∨ take = 1 := by omega
    rcases htakeCases with htake0 | htake1
    · simp [htake0]
    · simp [htake1]
  have hincM : inc < M := Nat.lt_of_le_of_lt hinc hTermM
  have hrun := accBody_run_mod c k i w radical phiSmall sqf phi g s
    hR hAcc hW hProd hPhi hSqf hG hOne hZero hi hr hIndexM hT hTi
    hRadPos hRadM hRadDvd hRadLe hPhiSmallM hPhiPos hPhiM hPhiEq
    hPrimes hSumM hTermM
  dsimp only at hrun
  have hge : g ≤ (g + inc) % M := by
    rw [← hrun.1]
    exact hNoDecrease
  have hsumM :=
    LeanCompCert.Ports.Prop1224CellGuardedSemantics.add_lt_word_of_mod_ge
      hGword hincM hge
  have hmod : (g + inc) % M = g + inc := Nat.mod_eq_of_lt hsumM
  rw [hmod] at hrun
  simpa only [cellMarkedStep, take, inc] using
    And.intro hsumM hrun

#print axioms accAddSuffix_run_mod
#print axioms accComputeSuffix_run_mod
#print axioms accBody_run_mod
#print axioms accBody_run_exact_of_no_decrease

end LeanCompCert.Ports.Prop1224Cell

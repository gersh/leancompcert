import LeanCompCert.Ports.R2SegLogPayload
import LeanCompCert.Ports.R2SegLogLinear

/-!
# Complete finished-event commit in the `R₂*` log phase

Instructions 263 through the term-counter commit decode the packed source
payload, select its source-level jump factors, compute the scaled jump and
error charge, and commit the signed event to the three carried accumulators.
This file composes those already verified literal slices without expanding
the intervening majorant block.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame

/-- Instructions 263--324, the complete payload-to-accumulator event. -/
def logFinalEventBody (c : R2Cfg) : List AInstr :=
  (c.logBody.drop 74).take 74

theorem logFinalEventBody_eq_stages (c : R2Cfg) :
    logFinalEventBody c =
      (logPayloadDecodeBody ++ logFactorBody) ++
        (logJumpErrorBody c.sc (ln2Up c.sc) ++
          logBetweenJumpAndCommitBody c ++ logAccumulatorCommitBody) := by
  rfl

/-- Exact composition of a finished source event through the literal
payload decoder, factor selector, jump/error calculation, and signed commit.
The `d` hypothesis names the post-linear accumulator produced by the
intervening majorant block, whose event registers are frame-proved here. -/
theorem logFinalEventBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (first aux mode lnN e d err terms : Nat) (positive : Bool) (u v : Nat)
    (hfactors : ClassResult.jumpFactors
      ⟨true, mode, first, aux⟩ lnN = (positive, u, v))
    (hmode : mode ≤ 3) (hmode0 : mode = 0 → first = 0)
    (hfirst : first < 2 ^ wtBits) (haux29 : aux < 2 ^ 29)
    (hpl : s.regs rPl = first + (aux <<< wtBits) + (mode <<< 57))
    (h242 : s.regs 242 = mode)
    (h243 : s.regs 243 = if 2 ≤ mode then 1 else 0)
    (h262 : s.regs 262 = lnN)
    (haux : aux ≤ lnN) (hlnM : lnN < M)
    (hfirstM : first < M) (hauxM : aux < M)
    (hsumM : first + (lnN - aux) < M)
    (he : s.regs rEx = e) (hfin : s.regs 247 = 1)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hS : c.sc < M) (hSm4 : c.sc - 4 < M) (hl2 : ln2Up c.sc < M)
    (huv : u * v < M)
    (hshift : ((u * v) <<< (if positive then 1 else 0)) < M)
    (he1 : e + 1 < M) (henum : (e + 1) * ln2Up c.sc < M)
    (hcharge : ((e + 1) * ln2Up c.sc / 2 ^ (c.sc - 4)) + 2 < M)
    (hd : (arun k
      (arun k
        (arun k s (logPayloadDecodeBody ++ logFactorBody))
        (logJumpErrorBody c.sc (ln2Up c.sc)))
      (logBetweenJumpAndCommitBody c)).regs rD = d)
    (hsub : positive = false →
      ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc ≤ d)
    (hdadd : positive = true →
      d + ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc < M)
    (hdM : d < M)
    (htermM : ((u * v) <<< (if positive then 1 else 0)) /
      2 ^ c.sc < M)
    (herradd : err +
      (((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2) < M)
    (htermsadd : terms + 1 < M) :
    let term := ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc
    let charge := ((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2
    let out := arun k s (logFinalEventBody c)
    out.regs rD = (if positive then d + term else d - term) ∧
      out.regs rErr = err + charge ∧ out.regs rTerms = terms + 1 ∧
      out.arr = s.arr := by
  let factored := arun k s (logPayloadDecodeBody ++ logFactorBody)
  have hfactor := logDecodeThroughFactorBody_run_exact k s
    first aux mode lnN hmode hmode0 hfirst haux29 hpl h242 h243 h262
    haux hlnM hfirstM hauxM hsumM
  dsimp only at hfactor
  have hvalues :
      (factored.regs 266, factored.regs 272, factored.regs 278) =
        (if positive then 1 else 0, u, v) := by
    simpa only [factored, hfactors] using hfactor.1
  have hpositive : factored.regs 266 = if positive then 1 else 0 :=
    congrArg (fun q => q.1) hvalues
  have hu : factored.regs 272 = u :=
    congrArg (fun q => q.2.1) hvalues
  have hv : factored.regs 278 = v :=
    congrArg (fun q => q.2.2) hvalues
  have frame (r : Nat)
      (hw : writes r (logPayloadDecodeBody ++ logFactorBody) = false) :
      factored.regs r = s.regs r :=
    arun_frame k r (logPayloadDecodeBody ++ logFactorBody) hw s
  have hjump := logJumpThroughCommitBody_run c k factored positive u v e
    d err terms hu hv hpositive
    ((frame rEx (by rfl)).trans he) ((frame 247 (by rfl)).trans hfin)
    ((frame rErr (by rfl)).trans herr)
    ((frame rTerms (by rfl)).trans hterms)
    hS hSm4 hl2 huv hshift he1 henum hcharge hd hsub hdadd hdM htermM
    herradd htermsadd
  dsimp only at hjump ⊢
  rw [logFinalEventBody_eq_stages, arun_append]
  exact ⟨hjump.1, hjump.2.1, hjump.2.2.1,
    hjump.2.2.2.trans hfactor.2⟩

/-- Finished-event composition with the linear accumulator derived from the
literal instruction stream, rather than supplied as an external hypothesis.
-/
theorem logFinalEventBody_linear_run (c : R2Cfg) (k : Nat) (s : AState)
    (first aux mode lnN e n prev d err terms : Nat)
    (positive : Bool) (u v : Nat)
    (hfactors : ClassResult.jumpFactors
      ⟨true, mode, first, aux⟩ lnN = (positive, u, v))
    (hmode : mode ≤ 3) (hmode0 : mode = 0 → first = 0)
    (hfirst : first < 2 ^ wtBits) (haux29 : aux < 2 ^ 29)
    (hpl : s.regs rPl = first + (aux <<< wtBits) + (mode <<< 57))
    (h242 : s.regs 242 = mode)
    (h243 : s.regs 243 = if 2 ≤ mode then 1 else 0)
    (h262 : s.regs 262 = lnN)
    (haux : aux ≤ lnN) (hlnM : lnN < M)
    (hfirstM : first < M) (hauxM : aux < M)
    (hsumM : first + (lnN - aux) < M)
    (he : s.regs rEx = e) (hfin : s.regs 247 = 1)
    (hne : s.regs rNe = n) (hprev : s.regs rPrev = prev)
    (hd : s.regs rD = d)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hS : c.sc < M) (hSm4 : c.sc - 4 < M) (hl2 : ln2Up c.sc < M)
    (huv : u * v < M)
    (hshift : ((u * v) <<< (if positive then 1 else 0)) < M)
    (he1 : e + 1 < M) (henum : (e + 1) * ln2Up c.sc < M)
    (hcharge : ((e + 1) * ln2Up c.sc / 2 ^ (c.sc - 4)) + 2 < M)
    (hprevn : prev < n) (hnM : n < M)
    (hgM : gammaStep c.sc < M) (hgap : n - prev < 65536)
    (hprodM : (n - prev - 1) * gammaStep c.sc < M)
    (hlinFirstM : d + (n - prev - 1) * gammaStep c.sc < M)
    (hlinearM : d + (n - prev) * gammaStep c.sc < M)
    (hsub : positive = false →
      ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc ≤
        d + (n - prev) * gammaStep c.sc)
    (hdadd : positive = true →
      d + (n - prev) * gammaStep c.sc +
        ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc < M)
    (htermM : ((u * v) <<< (if positive then 1 else 0)) /
      2 ^ c.sc < M)
    (herradd : err +
      (((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2) < M)
    (htermsadd : terms + 1 < M) :
    let linear := d + (n - prev) * gammaStep c.sc
    let term := ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc
    let charge := ((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2
    let out := arun k s (logFinalEventBody c)
    out.regs rD = (if positive then linear + term else linear - term) ∧
      out.regs rErr = err + charge ∧ out.regs rTerms = terms + 1 ∧
      out.arr = s.arr := by
  let factored := arun k s (logPayloadDecodeBody ++ logFactorBody)
  let afterJump := arun k factored
    (logJumpErrorBody c.sc (ln2Up c.sc))
  let linear := d + (n - prev) * gammaStep c.sc
  have frameFactor (r : Nat)
      (hw : writes r (logPayloadDecodeBody ++ logFactorBody) = false) :
      factored.regs r = s.regs r :=
    arun_frame k r (logPayloadDecodeBody ++ logFactorBody) hw s
  have frameJump (r : Nat)
      (hw : writes r (logJumpErrorBody c.sc (ln2Up c.sc)) = false) :
      afterJump.regs r = factored.regs r :=
    arun_frame k r (logJumpErrorBody c.sc (ln2Up c.sc)) hw factored
  have hlinear :
      (arun k afterJump (logBetweenJumpAndCommitBody c)).regs rD = linear :=
    logBetweenJumpAndCommitBody_linear_run c k afterJump n prev d
      ((frameJump rNe (by rfl)).trans ((frameFactor rNe (by rfl)).trans hne))
      ((frameJump rPrev (by rfl)).trans
        ((frameFactor rPrev (by rfl)).trans hprev))
      ((frameJump rD (by rfl)).trans ((frameFactor rD (by rfl)).trans hd))
      ((frameJump 247 (by rfl)).trans ((frameFactor 247 (by rfl)).trans hfin))
      hprevn hnM hgM hgap hprodM hlinFirstM hlinearM
  have hrun := logFinalEventBody_run c k s first aux mode lnN e linear err
    terms positive u v hfactors hmode hmode0 hfirst haux29 hpl h242 h243
    h262 haux hlnM hfirstM hauxM hsumM he hfin herr hterms hS hSm4 hl2
    huv hshift he1 henum hcharge hlinear hsub hdadd hlinearM htermM
    herradd htermsadd
  simpa only [linear] using hrun

#print axioms logFinalEventBody_eq_stages
#print axioms logFinalEventBody_run
#print axioms logFinalEventBody_linear_run

end LeanCompCert.Ports.R2SegSieve

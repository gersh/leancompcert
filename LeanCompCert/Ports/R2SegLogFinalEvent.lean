import LeanCompCert.Ports.R2SegLogPayload

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

#print axioms logFinalEventBody_eq_stages
#print axioms logFinalEventBody_run

end LeanCompCert.Ports.R2SegSieve

import LeanCompCert.Ports.R2SegLogFinalEvent

/-!
# Exact R₂ finished-event state before the underflow audit

This leaf stops the literal payload-to-accumulator path immediately before
the strengthened negative-subtraction audit.  It exposes the finish bit,
decoded sign, computed jump term, and post-linear accumulator without running
the signed commit and therefore without assuming the subtraction is defined.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

/-- The source-event suffix from payload decoding through the last linear and
comparison instruction, stopping exactly before `logUnderflowAuditBody`. -/
def logBeforeUnderflowEventBody (c : R2Cfg) : List AInstr :=
  (logPayloadDecodeBody ++ logFactorBody) ++
    logJumpErrorBody c.sc (ln2Up c.sc) ++
      logBetweenJumpAndCommitBody c

theorem logFinalEventBody_eq_before_underflow_stages (c : R2Cfg) :
    logFinalEventBody c =
      logBeforeUnderflowEventBody c ++ logUnderflowAuditBody ++
        logAccumulatorCommitBody := by
  rfl

/-- Exact decoded and linear state at the audit boundary.  All hypotheses are
ordinary no-wrap/decoder facts for the preceding literal islands; notably,
there is no negative-subtraction premise. -/
theorem logBeforeUnderflowEventBody_run
    (c : R2Cfg) (k : Nat) (s : AState)
    (first aux mode lnN e n prev d : Nat)
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
    (hS : c.sc < M) (hSm4 : c.sc - 4 < M)
    (hl2 : ln2Up c.sc < M) (huv : u * v < M)
    (hshift : ((u * v) <<< (if positive then 1 else 0)) < M)
    (he1 : e + 1 < M) (henum : (e + 1) * ln2Up c.sc < M)
    (hcharge : ((e + 1) * ln2Up c.sc / 2 ^ (c.sc - 4)) + 2 < M)
    (hprevn : prev < n) (hnM : n < M)
    (hgM : gammaStep c.sc < M) (hgap : n - prev < 65536)
    (hprodM : (n - prev - 1) * gammaStep c.sc < M)
    (hfirstLinearM : d + (n - prev - 1) * gammaStep c.sc < M)
    (hlinearM : d + (n - prev) * gammaStep c.sc < M) :
    let term := ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc
    let linear := d + (n - prev) * gammaStep c.sc
    let out := arun k s (logBeforeUnderflowEventBody c)
    out.regs 247 = 1 ∧
      out.regs 266 = (if positive then 1 else 0) ∧
      out.regs 281 = term ∧ out.regs rD = linear := by
  dsimp only
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
    congrArg (fun x => x.1) hvalues
  have hu : factored.regs 272 = u :=
    congrArg (fun x => x.2.1) hvalues
  have hv : factored.regs 278 = v :=
    congrArg (fun x => x.2.2) hvalues
  have factorFrame (r : Nat)
      (hw : writes r (logPayloadDecodeBody ++ logFactorBody) = false) :
      factored.regs r = s.regs r :=
    arun_frame k r (logPayloadDecodeBody ++ logFactorBody) hw s
  let jumped := arun k factored
    (logJumpErrorBody c.sc (ln2Up c.sc))
  have hjump := logJumpErrorBody_run k factored c.sc (ln2Up c.sc)
    u v (if positive then 1 else 0) e hu hv hpositive
    ((factorFrame rEx (by rfl)).trans he) hS hSm4 hl2 huv hshift
    he1 henum hcharge
  dsimp only at hjump
  have jumpFrame (r : Nat)
      (hw : writes r (logJumpErrorBody c.sc (ln2Up c.sc)) = false) :
      jumped.regs r = factored.regs r :=
    arun_frame k r (logJumpErrorBody c.sc (ln2Up c.sc)) hw factored
  let out := arun k jumped (logBetweenJumpAndCommitBody c)
  have hlinear := logBetweenJumpAndCommitBody_linear_run c k jumped
    n prev d
    ((jumpFrame rNe (by rfl)).trans ((factorFrame rNe (by rfl)).trans hne))
    ((jumpFrame rPrev (by rfl)).trans
      ((factorFrame rPrev (by rfl)).trans hprev))
    ((jumpFrame rD (by rfl)).trans ((factorFrame rD (by rfl)).trans hd))
    ((jumpFrame 247 (by rfl)).trans
      ((factorFrame 247 (by rfl)).trans hfin))
    hprevn hnM hgM hgap hprodM hfirstLinearM hlinearM
  have hbetween := logBetweenJumpAndCommitBody_frame c k jumped
  dsimp only at hbetween
  have houtFin : out.regs 247 = 1 :=
    hbetween.2.1.trans <|
      (jumpFrame 247 (by rfl)).trans ((factorFrame 247 (by rfl)).trans hfin)
  have houtPositive : out.regs 266 = if positive then 1 else 0 :=
    hbetween.1.trans <| (jumpFrame 266 (by rfl)).trans hpositive
  have houtTerm : out.regs 281 =
      ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc :=
    hbetween.2.2.1.trans hjump.1
  rw [logBeforeUnderflowEventBody, arun_append, arun_append]
  exact ⟨houtFin, houtPositive, houtTerm, hlinear⟩

#print axioms logFinalEventBody_eq_before_underflow_stages
#print axioms logBeforeUnderflowEventBody_run

end LeanCompCert.Ports.R2SegSieve

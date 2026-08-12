import LeanCompCert.Ports.CDEMAbelSieveScheduledTable
import LeanCompCert.Ports.CDEMAbelMarkPlane

/-! # The scheduled CDEM sieve-to-marking boundary -/

namespace LeanCompCert.Ports.CDEMAbelSieveMarkEntry

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveSchedule
open LeanCompCert.Ports.CDEMAbelSieveScheduledTable
open LeanCompCert.Ports.CDEMAbelSieveReady

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- During a scheduled sieve iteration the inactive window tail leaves the
window counter and origin unchanged. -/
theorem body_sieve_preserves_rR_rW (c : Cfg) (idx : Nat) (st : AState)
    (w : Nat) (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hidx : idx < c.sieveLen) (hperiodPos : 0 < c.period)
    (hperiodM : c.period < M) (hwM : w < M)
    (hR : st.regs rR = 0) (hW : st.regs rW = w) :
    let out := arun idx st c.body
    out.regs rR = 0 ∧ out.regs rW = w := by
  let selected := arun idx st c.selectors
  let sieved := arun idx selected c.sieveBody
  let marked := arun idx sieved c.markBody
  let headed := arun idx marked c.accHead
  let produced := arun idx headed c.accProd
  let accumulated := arun idx produced c.accBisect
  let out := arun idx accumulated c.tailBody
  have hsel := selectors_sieve_run c idx st hidxM hsieveM hidx
  have selectedFrame (r : Nat)
      (hwrites : ArrayRegFrame.writes r c.selectors = false) :
      selected.regs r = st.regs r :=
    ArrayRegFrame.arun_frame idx r c.selectors hwrites st
  have sievedFrame (r : Nat)
      (hwrites : ArrayRegFrame.writes r c.sieveBody = false) :
      sieved.regs r = selected.regs r :=
    ArrayRegFrame.arun_frame idx r c.sieveBody hwrites selected
  have markedFrame (r : Nat)
      (hwrites : ArrayRegFrame.writes r c.markBody = false) :
      marked.regs r = sieved.regs r :=
    ArrayRegFrame.arun_frame idx r c.markBody hwrites sieved
  have headedFrame (r : Nat)
      (hwrites : ArrayRegFrame.writes r c.accHead = false) :
      headed.regs r = marked.regs r :=
    ArrayRegFrame.arun_frame idx r c.accHead hwrites marked
  have producedFrame (r : Nat)
      (hwrites : ArrayRegFrame.writes r c.accProd = false) :
      produced.regs r = headed.regs r :=
    ArrayRegFrame.arun_frame idx r c.accProd hwrites headed
  have accumulatedFrame (r : Nat)
      (hwrites : ArrayRegFrame.writes r c.accBisect = false) :
      accumulated.regs r = produced.regs r :=
    ArrayRegFrame.arun_frame idx r c.accBisect hwrites produced
  have h41 : accumulated.regs 41 = 0 :=
    (accumulatedFrame 41 (by rfl)).trans
      ((producedFrame 41 (by rfl)).trans
        ((headedFrame 41 (by rfl)).trans
          ((markedFrame 41 (by rfl)).trans
            ((sievedFrame 41 (by rfl)).trans hsel.2.1))))
  have haccR : accumulated.regs rR = 0 :=
    (accumulatedFrame rR (by rfl)).trans
      ((producedFrame rR (by rfl)).trans
        ((headedFrame rR (by rfl)).trans
          ((markedFrame rR (by rfl)).trans
            ((sievedFrame rR (by rfl)).trans
              ((selectedFrame rR (by rfl)).trans hR)))))
  have haccW : accumulated.regs rW = w :=
    (accumulatedFrame rW (by rfl)).trans
      ((producedFrame rW (by rfl)).trans
        ((headedFrame rW (by rfl)).trans
          ((markedFrame rW (by rfl)).trans
            ((sievedFrame rW (by rfl)).trans
              ((selectedFrame rW (by rfl)).trans hW)))))
  have haccR' : accumulated.regs 2 = 0 := by simpa [rR] using haccR
  have haccW' : accumulated.regs 3 = w := by simpa [rW] using haccW
  change out.regs rR = 0 ∧ out.regs rW = w
  simp [out, Cfg.tailBody, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
    h41, haccR', haccW', rR, rW, Nat.mod_eq_of_lt hperiodM,
    Nat.ne_of_lt hperiodPos, Nat.mod_eq_of_lt hwM]

theorem sieveEntry_rR_rW (c : Cfg) :
    (sieveEntry c).regs rR = 0 ∧ (sieveEntry c).regs rW = 1 := by
  unfold sieveEntry Cfg.init
  rw [arun_append]
  simp [Cfg.seedList, seedRegs, arun, astep, AState.writeReg,
    InstrBlock.sdest, InstrBlock.sval, denoteOperand, rZero, rR, rW, rD,
    rSg, rJ, rN, rPj, rM, rPar, rSqf, rF, rE, rKr, rC, rDp, rDn,
    rSl, rSh, rT, rT2, rViol, rUpLo, rUpHi, rUnLo, rUnHi, rVLo,
    rVHi, rTv, rK, M]

set_option maxHeartbeats 3000000 in
theorem bodySieveIter_preserves_rR_rW (c : Cfg) (count : Nat)
    (st : AState) (w : Nat) (hcount : count ≤ c.sieveLen)
    (hsieveM : c.sieveLen < M) (hperiodPos : 0 < c.period)
    (hperiodM : c.period < M) (hwM : w < M)
    (hR : st.regs rR = 0) (hW : st.regs rW = w) :
    let out := bodySieveIter c count st
    out.regs rR = 0 ∧ out.regs rW = w := by
  induction count with
  | zero => simpa [bodySieveIter] using And.intro hR hW
  | succ count ih =>
      have hcountLt : count < c.sieveLen := by omega
      have hpre := ih (by omega)
      have hstep := body_sieve_preserves_rR_rW c count
        (bodySieveIter c count st) w (by omega) hsieveM hcountLt
        hperiodPos hperiodM hwM hpre.1 hpre.2
      simpa [bodySieveIter] using hstep

/-- The real scheduled sieve prefix reaches the first marking selector with
the resident table complete and with the initial window still untouched. -/
theorem initialized_scheduled_sieve_mark_entry (c : Cfg)
    (hpnPos : 0 < c.pn) (hpnM : c.pn < M)
    (hsieveM : c.sieveLen < M) (hsinkM : c.sink < M)
    (hperiodPos : 0 < c.period) (hperiodM : c.period < M)
    (hprimePos : ∀ p ∈ c.primes, 0 < p)
    (hprimeM : ∀ p ∈ c.primes, p < M)
    (hprimes : c.primes = Ref.muPrimes c.kBound) :
    let out := (List.range c.sieveLen).foldl
      (fun s idx => arun idx s c.body) (sieveEntry c)
    out.regs rR = 0 ∧ out.regs rW = 1 ∧ out.regs rZero = 0 ∧
      (∀ j, out.arr j < M) ∧
      (∀ d, 1 ≤ d → d ≤ c.kBound →
        out.arr (d + c.muBase) = Ref.muCodeFor c.kBound d) := by
  have hfold := bodySieveIter_eq_fold c c.sieveLen (sieveEntry c)
  have hcursor := bodySieveIter_preserves_rR_rW c c.sieveLen
    (sieveEntry c) 1 (by omega) hsieveM hperiodPos hperiodM
    (by decide) (sieveEntry_rR_rW c).1 (sieveEntry_rR_rW c).2
  rcases bodySieveIter_invariant c c.sieveLen (sieveEntry c)
    (initialSieveModel c) (sieveEntry_preRep c)
    (initialSieveModel_cursor c hpnPos hprimePos hpnM hprimeM)
    (initialSieveModel_table c hpnM hprimeM)
    (by simp [sieveRank, initialSieveModel]) (by omega)
    hsieveM hpnM hsinkM with ⟨model, hrep, _, _, _⟩
  have htable := initialized_scheduled_sieve_full_muCodeFor c hpnPos hpnM
    hsieveM hsinkM hprimePos hprimeM hprimes
  rw [← hfold]
  refine ⟨hcursor.1, hcursor.2, hrep.zero, hrep.arrWord, ?_⟩
  intro d hd hdK
  rw [hfold]
  exact htable d (by unfold Cfg.k1; omega)

end LeanCompCert.Ports.CDEMAbelSieveMarkEntry

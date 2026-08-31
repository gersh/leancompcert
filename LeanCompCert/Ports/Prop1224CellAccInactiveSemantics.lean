import LeanCompCert.Ports.Prop1224CellAccArraySemantics

/-!
# Inactive accumulation-body array denotation

Outside the accumulation phase, the same literal body executes with gate
register `12 = 0`.  It still writes its four dedicated sink cells, but must
frame every live plane.  This small theorem is the embedding seam needed by
the marking and log-phase telescopes.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame

/-- With the accumulation gate clear, the position multiplier selects
logical offset zero independently of the stale round register. -/
theorem accPositionPrefix_inactive_index
    (c : CellCfg) (k : Nat) (s : AState)
    (hAcc : s.regs 12 = 0) :
    (arun k s (accPositionPrefix c)).regs 86 = 0 := by
  simp [accPositionPrefix, arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp, hAcc]

/-- The gated accumulator addition is literally the identity when the
accumulation selector is clear.  The sole word hypothesis is the ordinary
machine-state invariant needed to simplify the final reduction modulo
`2^64`; no value of the expensive term is inspected. -/
theorem accAddSuffix_inactive_rG
    (k : Nat) (s : AState) (hAcc : s.regs 12 = 0)
    (hGWord : s.regs rG < M) :
    (arun k s accAddSuffix).regs rG = s.regs rG := by
  have hG180 : s.regs 180 = s.regs rG := by simp [rG]
  simp [accAddSuffix, arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    rG, hAcc, hG180, Nat.mod_eq_of_lt hGWord]

/-- The complete arithmetic suffix preserves the running accumulator while
its selector is clear, independently of the loaded cell or ceiling term. -/
theorem accComputeSuffix_inactive_rG
    (k : Nat) (s : AState) (hAcc : s.regs 12 = 0)
    (hGWord : s.regs rG < M) :
    (arun k s accComputeSuffix).regs rG = s.regs rG := by
  let gated := arun k s accGateSuffix
  let ceiled := arun k gated accCeilSuffix
  have hAccGated : gated.regs 12 = 0 :=
    (arun_frame k 12 accGateSuffix (by rfl) s).trans hAcc
  have hAccCeiled : ceiled.regs 12 = 0 :=
    (arun_frame k 12 accCeilSuffix (by rfl) gated).trans hAccGated
  have hGGated : gated.regs rG = s.regs rG :=
    arun_frame k rG accGateSuffix (by rfl) s
  have hGCeiled : ceiled.regs rG = s.regs rG :=
    (arun_frame k rG accCeilSuffix (by rfl) gated).trans hGGated
  have hGCeiledWord : ceiled.regs rG < M := by
    rw [hGCeiled]
    exact hGWord
  have hadd := accAddSuffix_inactive_rG k ceiled hAccCeiled hGCeiledWord
  rw [accComputeSuffix, arun_append, arun_append]
  exact hadd.trans hGCeiled

/-- In an inactive accumulation body, the persistent running accumulator is
framed by the literal prefix, coprimality chain, gated compute suffix, and
reset stores. -/
theorem accBody_inactive_rG
    (c : CellCfg) (k : Nat) (s : AState)
    (hAcc : s.regs 12 = 0) (hGWord : s.regs rG < M) :
    (arun k s c.accBody).regs rG = s.regs rG := by
  let pref := arun k s (accPrefix c)
  let copied := arun k pref (coprimeBody c.qPrimes)
  let computed := arun k copied accComputeSuffix
  let resetAddr := arun k computed (accResetAddressSuffix c)
  have hpG : pref.regs rG = s.regs rG :=
    arun_frame k rG (accPrefix c) (by rfl) s
  have hpAcc : pref.regs 12 = 0 :=
    (arun_frame k 12 (accPrefix c) (by rfl) s).trans hAcc
  have hcG : copied.regs rG = s.regs rG :=
    (coprimeBody_reg_frame c.qPrimes rG k pref
      (by decide) (by decide) (by decide)).trans hpG
  have hcAcc : copied.regs 12 = 0 :=
    (coprimeBody_reg_frame c.qPrimes 12 k pref
      (by decide) (by decide) (by decide)).trans hpAcc
  have hcGWord : copied.regs rG < M := by
    rw [hcG]
    exact hGWord
  have hcomputedG : computed.regs rG = s.regs rG :=
    (accComputeSuffix_inactive_rG k copied hcAcc hcGWord).trans hcG
  have hresetAddrG : resetAddr.regs rG = s.regs rG :=
    (arun_frame k rG (accResetAddressSuffix c) (by rfl) computed).trans
      hcomputedG
  have hstoresG :
      (arun k resetAddr accResetStoreSuffix).regs rG = s.regs rG :=
    (arun_frame k rG accResetStoreSuffix (by rfl) resetAddr).trans
      hresetAddrG
  rw [accBody_eq, arun_append, arun_append, accSuffix, arun_append,
    accResetSuffix, arun_append]
  exact hstoresG

/-- The store-free prefix of an inactive accumulation body selects exactly
the four sink addresses `4L,5L,6L,7L`. -/
theorem accBeforeResetStores_inactive_addresses
    (c : CellCfg) (k : Nat) (s : AState)
    (hAcc : s.regs 12 = 0) (h7L : 7 * c.segLen < M) :
    let pre := arun k s (accBeforeResetStores c)
    pre.regs 108 = 4 * c.segLen ∧
      pre.regs 109 = 5 * c.segLen ∧
      pre.regs 110 = 6 * c.segLen ∧
      pre.regs 111 = 7 * c.segLen := by
  let positioned := arun k s (accPositionPrefix c)
  let loaded := arun k positioned accLoadPrefix
  let classified := arun k loaded accClassifyPrefix
  let copied := arun k classified (coprimeBody c.qPrimes)
  let computed := arun k copied accComputeSuffix
  have h86Positioned : positioned.regs 86 = 0 :=
    accPositionPrefix_inactive_index c k s hAcc
  have h86Loaded : loaded.regs 86 = 0 :=
    (arun_frame k 86 accLoadPrefix (by rfl) positioned).trans h86Positioned
  have h86Classified : classified.regs 86 = 0 :=
    (arun_frame k 86 accClassifyPrefix (by rfl) loaded).trans h86Loaded
  have h86Copied : copied.regs 86 = 0 :=
    (coprimeBody_reg_frame c.qPrimes 86 k classified
      (by decide) (by decide) (by decide)).trans h86Classified
  have h86Computed : computed.regs 86 = 0 :=
    (arun_frame k 86 accComputeSuffix (by rfl) copied).trans h86Copied
  have hAccComputed : computed.regs 12 = 0 :=
    (arun_frame k 12 accComputeSuffix (by rfl) copied).trans
      ((coprimeBody_reg_frame c.qPrimes 12 k classified
        (by decide) (by decide) (by decide)).trans
        ((arun_frame k 12 accClassifyPrefix (by rfl) loaded).trans
          ((arun_frame k 12 accLoadPrefix (by rfl) positioned).trans
            ((arun_frame k 12 (accPositionPrefix c) (by rfl) s).trans hAcc))))
  have h4L : 4 * c.segLen < M := by omega
  have h5L : 5 * c.segLen < M := by omega
  have h6L : 6 * c.segLen < M := by omega
  have hOne : (1 : Nat) < M := by decide
  have h45 : 4 * c.segLen + c.segLen = 5 * c.segLen := by omega
  have h46 : 4 * c.segLen + 2 * c.segLen = 6 * c.segLen := by omega
  have h47 : 4 * c.segLen + 3 * c.segLen = 7 * c.segLen := by omega
  have haddrs :
      let out := arun k computed (accResetAddressSuffix c)
      out.regs 108 = 4 * c.segLen ∧
        out.regs 109 = 5 * c.segLen ∧
        out.regs 110 = 6 * c.segLen ∧
        out.regs 111 = 7 * c.segLen := by
    simp [accResetAddressSuffix, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      CellCfg.sink, h86Computed, hAccComputed,
      h45, h46, h47, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt h4L,
      Nat.mod_eq_of_lt h5L, Nat.mod_eq_of_lt h6L,
      Nat.mod_eq_of_lt h7L]
  simpa [accBeforeResetStores, accPrefix, positioned, loaded, classified,
    copied, computed, arun_append] using haddrs

/-- Complete functional-array result of an inactive accumulation body. -/
theorem accBody_inactive_arr_eq
    (c : CellCfg) (k : Nat) (s : AState)
    (hAcc : s.regs 12 = 0) (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0) (h7L : 7 * c.segLen < M) :
    let out := arun k s c.accBody
    out.arr =
      (writeP1224AccCell s c.segLen (4 * c.segLen)
        (out.regs rG)).arr := by
  let pre := arun k s (accBeforeResetStores c)
  let out := arun k pre accResetStoreSuffix
  have haddrs := accBeforeResetStores_inactive_addresses c k s hAcc h7L
  dsimp only at haddrs
  have hOnePre : pre.regs rOne = 1 :=
    (accBeforeResetStores_reg_frame c rOne k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl)).trans hOne
  have hZeroPre : pre.regs rZero = 0 :=
    (accBeforeResetStores_reg_frame c rZero k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl)).trans hZero
  have hOutReg : out.regs rG = pre.regs rG :=
    arun_frame k rG accResetStoreSuffix (by rfl) pre
  have h109 : pre.regs 109 = 4 * c.segLen + c.segLen := by
    rw [haddrs.2.1]
    omega
  have h110 : pre.regs 110 = 4 * c.segLen + 2 * c.segLen := by
    rw [haddrs.2.2.1]
    omega
  have h111 : pre.regs 111 = 4 * c.segLen + 3 * c.segLen := by
    rw [haddrs.2.2.2]
    omega
  have hstores := accResetStoreSuffix_arr_eq c k (4 * c.segLen)
    (pre.regs rG) pre haddrs.1 h109 h110 h111
    rfl hOnePre hZeroPre (by omega)
  have harr := accBeforeResetStores_arr_frame c k s
  rw [accBody_eq_before_reset_stores, arun_append]
  change out.arr =
    (writeP1224AccCell s c.segLen (4 * c.segLen) (out.regs rG)).arr
  rw [hstores, hOutReg]
  exact writeP1224AccCell_arr_congr c.segLen (4 * c.segLen)
    (pre.regs rG) harr

/-- Inactive accumulation therefore frames every address in the four live
planes. -/
theorem accBody_inactive_live_frame
    (c : CellCfg) (k : Nat) (s : AState) (a : Nat)
    (hAcc : s.regs 12 = 0) (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0) (h7L : 7 * c.segLen < M)
    (ha : a < 4 * c.segLen) :
    (arun k s c.accBody).arr a = s.arr a := by
  have harr := accBody_inactive_arr_eq c k s hAcc hOne hZero h7L
  dsimp only at harr
  rw [harr]
  apply writeP1224AccCell_frame <;> omega

/-- Register frame for the complete accumulation body.  The hypotheses are
small syntactic checks for the fixed prefixes plus the three row-dependent
coprimality temporaries. -/
theorem accBody_reg_frame
    (c : CellCfg) (reg k : Nat) (s : AState)
    (hprefix : LeanCompCert.Verified.ArrayRegFrame.writes reg
      (accPrefix c) = false)
    (h81 : reg ≠ 81) (h82 : reg ≠ 82) (h83 : reg ≠ 83)
    (hcompute : LeanCompCert.Verified.ArrayRegFrame.writes reg
      accComputeSuffix = false)
    (haddress : LeanCompCert.Verified.ArrayRegFrame.writes reg
      (accResetAddressSuffix c) = false)
    (hstores : LeanCompCert.Verified.ArrayRegFrame.writes reg
      accResetStoreSuffix = false) :
    (arun k s c.accBody).regs reg = s.regs reg := by
  let pre := arun k s (accBeforeResetStores c)
  have hp : pre.regs reg = s.regs reg :=
    accBeforeResetStores_reg_frame c reg k s hprefix h81 h82 h83
      hcompute haddress
  rw [accBody_eq_before_reset_stores, arun_append]
  exact (arun_frame k reg accResetStoreSuffix hstores pre).trans hp

#print axioms accPositionPrefix_inactive_index
#print axioms accAddSuffix_inactive_rG
#print axioms accComputeSuffix_inactive_rG
#print axioms accBody_inactive_rG
#print axioms accBeforeResetStores_inactive_addresses
#print axioms accBody_inactive_arr_eq
#print axioms accBody_inactive_live_frame
#print axioms accBody_reg_frame

end LeanCompCert.Ports.Prop1224Cell

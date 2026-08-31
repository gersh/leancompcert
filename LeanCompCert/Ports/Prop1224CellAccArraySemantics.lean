import LeanCompCert.Ports.Prop1224CellAccBodySemantics
import LeanCompCert.Ports.Prop1224CellMarkModel
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Exact array update of an active Proposition 12.2.4 accumulation cell

The scalar accumulation theorem exposes the four cells it writes.  For a
symbolic telescope we also need to know that every other cell is framed.
This file records the complete functional-array update of the literal store
suffix.  It is independent of the segment size and never evaluates a sweep.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame

/-- The four active-cell stores, in their literal execution order. -/
def writeP1224AccCell (s : AState) (L i value : Nat) : AState :=
  (((s.writeArr (i + 3 * L) value).writeArr i 1).writeArr (i + L) 1).writeArr
    (i + 2 * L) 0

/-- Complete array denotation of the four literal active-cell stores. -/
theorem accResetStoreSuffix_arr_eq (c : CellCfg) (k i value : Nat)
    (s : AState)
    (h108 : s.regs 108 = i) (h109 : s.regs 109 = i + c.segLen)
    (h110 : s.regs 110 = i + 2 * c.segLen)
    (h111 : s.regs 111 = i + 3 * c.segLen)
    (hG : s.regs rG = value) (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0)
    (hIndexM : i + 3 * c.segLen < M) :
    (arun k s accResetStoreSuffix).arr =
      (writeP1224AccCell s c.segLen i value).arr := by
  have hiM : i < M := by omega
  have hiL : i + c.segLen < M := by omega
  have hi2L : i + 2 * c.segLen < M := by omega
  funext a
  simp [accResetStoreSuffix, arun, astep, writeP1224AccCell,
    AState.writeArr, h108, h109, h110, h111, hG, hOne, hZero,
    Nat.mod_eq_of_lt hiM, Nat.mod_eq_of_lt hiL,
    Nat.mod_eq_of_lt hi2L, Nat.mod_eq_of_lt hIndexM]

/-- A four-cell active update frames every address other than its four
explicit targets. -/
theorem writeP1224AccCell_frame (s : AState) (L i value a : Nat)
    (h0 : a ≠ i) (h1 : a ≠ i + L) (h2 : a ≠ i + 2 * L)
    (h3 : a ≠ i + 3 * L) :
    (writeP1224AccCell s L i value).arr a = s.arr a := by
  simp [writeP1224AccCell, AState.writeArr, h0, h1, h2, h3]

theorem writeP1224AccCell_arr_congr {s t : AState} (L i value : Nat)
    (harr : s.arr = t.arr) :
    (writeP1224AccCell s L i value).arr =
      (writeP1224AccCell t L i value).arr := by
  funext a
  simp only [writeP1224AccCell, AState.writeArr]
  rw [harr]

/-- In particular, an earlier active accumulation cell cannot change any of
the three marking words of a later live cell. -/
theorem writeP1224AccCell_later_planes
    (s : AState) (L i j value : Nat) (hi : i < j) (hj : j < L) :
    p1224PlaneWordsAt (writeP1224AccCell s L i value) L j =
      p1224PlaneWordsAt s L j := by
  apply P1224PlaneWords.extensional <;>
    simp only [p1224PlaneWordsAt]
  · exact writeP1224AccCell_frame s L i value j
      (by omega) (by omega) (by omega) (by omega)
  · exact writeP1224AccCell_frame s L i value (j + L)
      (by omega) (by omega) (by omega) (by omega)
  · exact writeP1224AccCell_frame s L i value (j + 2 * L)
      (by omega) (by omega) (by omega) (by omega)

/-! ## Lifting the store denotation to the complete active body -/

/-- Everything in an accumulation body before its final four stores. -/
def accBeforeResetStores (c : CellCfg) : List AInstr :=
  accPrefix c ++ coprimeBody c.qPrimes ++ accComputeSuffix ++
    accResetAddressSuffix c

theorem accBody_eq_before_reset_stores (c : CellCfg) :
    c.accBody = accBeforeResetStores c ++ accResetStoreSuffix := by
  rw [accBody_eq]
  simp [accBeforeResetStores, accSuffix, accResetSuffix,
    List.append_assoc]

theorem coprimeBody_all_avoidsStore (ps : List Nat) :
    (coprimeBody ps).all
      LeanCompCert.Ports.ArraySegMobiusSignal.avoidsStore = true := by
  simp only [coprimeBody, List.all_flatMap]
  exact List.all_eq_true.mpr (fun _ _ => by rfl)

theorem accBeforeResetStores_arr_frame (c : CellCfg) (k : Nat)
    (s : AState) :
    (arun k s (accBeforeResetStores c)).arr = s.arr := by
  have hp : (accPrefix c).all
      LeanCompCert.Ports.ArraySegMobiusSignal.avoidsStore = true := by rfl
  have hc : accComputeSuffix.all
      LeanCompCert.Ports.ArraySegMobiusSignal.avoidsStore = true := by rfl
  have ha : (accResetAddressSuffix c).all
      LeanCompCert.Ports.ArraySegMobiusSignal.avoidsStore = true := by rfl
  exact LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame k
    (accBeforeResetStores c) s (by
      simpa only [accBeforeResetStores, List.all_append, hp, hc, ha,
        coprimeBody_all_avoidsStore, Bool.true_and])

/-- Register frame for the store-free accumulation prefix.  The only
row-dependent destinations are the three coprimality temporaries. -/
theorem accBeforeResetStores_reg_frame (c : CellCfg) (reg k : Nat)
    (s : AState)
    (hprefix : writes reg (accPrefix c) = false)
    (h81 : reg ≠ 81) (h82 : reg ≠ 82) (h83 : reg ≠ 83)
    (hcompute : writes reg accComputeSuffix = false)
    (haddress : writes reg (accResetAddressSuffix c) = false) :
    (arun k s (accBeforeResetStores c)).regs reg = s.regs reg := by
  let pref := arun k s (accPrefix c)
  let copied := arun k pref (coprimeBody c.qPrimes)
  let computed := arun k copied accComputeSuffix
  have hp : pref.regs reg = s.regs reg :=
    arun_frame k reg (accPrefix c) hprefix s
  have hc : copied.regs reg = pref.regs reg :=
    coprimeBody_reg_frame c.qPrimes reg k pref h81 h82 h83
  have hm : computed.regs reg = copied.regs reg :=
    arun_frame k reg accComputeSuffix hcompute copied
  have ha : (arun k computed (accResetAddressSuffix c)).regs reg =
      computed.regs reg :=
    arun_frame k reg (accResetAddressSuffix c) haddress computed
  simpa [accBeforeResetStores, pref, copied, computed, arun_append] using
    ha.trans (hm.trans (hc.trans hp))

/-- On an active accumulation round, the store addresses at the end of the
complete literal prefix are exactly the four planes of source cell `i`. -/
theorem accBeforeResetStores_addresses
    (c : CellCfg) (k i w : Nat) (s : AState)
    (hR : s.regs rR = c.markSteps + i) (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w) (hT : c.markSteps < M)
    (hTi : c.markSteps + i < M) (hr : w + i < M)
    (hIndexM : i + 3 * c.segLen < M) :
    let pre := arun k s (accBeforeResetStores c)
    pre.regs 108 = i ∧ pre.regs 109 = i + c.segLen ∧
      pre.regs 110 = i + 2 * c.segLen ∧
      pre.regs 111 = i + 3 * c.segLen := by
  let positioned := arun k s (accPositionPrefix c)
  have hp := accPositionPrefix_run c k i w s hR hAcc hW hT hTi hr hIndexM
  dsimp only at hp
  let loaded := arun k positioned accLoadPrefix
  let classified := arun k loaded accClassifyPrefix
  let copied := arun k classified (coprimeBody c.qPrimes)
  let computed := arun k copied accComputeSuffix
  have h86Loaded : loaded.regs 86 = i :=
    (arun_frame k 86 accLoadPrefix (by rfl) positioned).trans hp.1
  have h86Classified : classified.regs 86 = i :=
    (arun_frame k 86 accClassifyPrefix (by rfl) loaded).trans h86Loaded
  have h86Copied : copied.regs 86 = i :=
    (coprimeBody_reg_frame c.qPrimes 86 k classified
      (by decide) (by decide) (by decide)).trans h86Classified
  have h86Computed : computed.regs 86 = i :=
    (arun_frame k 86 accComputeSuffix (by rfl) copied).trans h86Copied
  have hAccComputed : computed.regs 12 = 1 :=
    (arun_frame k 12 accComputeSuffix (by rfl) copied).trans
      ((coprimeBody_reg_frame c.qPrimes 12 k classified
        (by decide) (by decide) (by decide)).trans
        ((arun_frame k 12 accClassifyPrefix (by rfl) loaded).trans
          ((arun_frame k 12 accLoadPrefix (by rfl) positioned).trans
            ((arun_frame k 12 (accPositionPrefix c) (by rfl) s).trans hAcc))))
  have ha := accResetAddressSuffix_run c k i computed h86Computed
    hAccComputed hIndexM
  dsimp only at ha
  simpa [accBeforeResetStores, accPrefix, positioned, loaded, classified,
    copied, computed, arun_append] using ha

/-- Complete functional-array denotation of an active accumulation body.
The accumulated value is deliberately named by the body's own output
register, so this framing theorem needs no arithmetic source assumptions. -/
theorem accBody_active_arr_eq
    (c : CellCfg) (k i w : Nat) (s : AState)
    (hR : s.regs rR = c.markSteps + i) (hAcc : s.regs 12 = 1)
    (hW : s.regs rW = w) (hOne : s.regs rOne = 1)
    (hZero : s.regs rZero = 0) (hT : c.markSteps < M)
    (hTi : c.markSteps + i < M) (hr : w + i < M)
    (hIndexM : i + 3 * c.segLen < M) :
    let out := arun k s c.accBody
    out.arr = (writeP1224AccCell s c.segLen i (out.regs rG)).arr := by
  let pre := arun k s (accBeforeResetStores c)
  let out := arun k pre accResetStoreSuffix
  have haddrs := accBeforeResetStores_addresses c k i w s hR hAcc hW hT
    hTi hr hIndexM
  dsimp only at haddrs
  have hOnePre : pre.regs rOne = 1 :=
    (accBeforeResetStores_reg_frame c rOne k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl)).trans hOne
  have hZeroPre : pre.regs rZero = 0 :=
    (accBeforeResetStores_reg_frame c rZero k s (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl)).trans hZero
  have hOutReg : out.regs rG = pre.regs rG :=
    arun_frame k rG accResetStoreSuffix (by rfl) pre
  have hstores := accResetStoreSuffix_arr_eq c k i (pre.regs rG) pre
    haddrs.1 haddrs.2.1 haddrs.2.2.1 haddrs.2.2.2 rfl hOnePre hZeroPre
    hIndexM
  have harr := accBeforeResetStores_arr_frame c k s
  rw [accBody_eq_before_reset_stores, arun_append]
  change out.arr =
    (writeP1224AccCell s c.segLen i (out.regs rG)).arr
  rw [hstores, hOutReg]
  exact writeP1224AccCell_arr_congr c.segLen i (pre.regs rG) harr

#print axioms accResetStoreSuffix_arr_eq
#print axioms writeP1224AccCell_frame
#print axioms writeP1224AccCell_later_planes
#print axioms accBeforeResetStores_addresses
#print axioms accBody_active_arr_eq

end LeanCompCert.Ports.Prop1224Cell

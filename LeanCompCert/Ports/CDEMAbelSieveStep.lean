import LeanCompCert.Ports.CDEMAbelSievePrefix

/-! # Non-final rows of the CDEM resident Möbius sieve -/

namespace LeanCompCert.Ports.CDEMAbelSieveStep

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelSieve
open LeanCompCert.Ports.CDEMAbelSievePrefix

/-- On a non-final prime, the suffix sends the provisional code to the sink,
advances only the prime cursor, and frames every live array cell. -/
theorem sieve_nonlast_suffix (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hlast : st.regs 64 = 0)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hpjNextM : st.regs rPj + 1 < M) (hword : ∀ j, st.regs j < M) :
    let out := arun idx st (sieveInactiveSuffix c)
    out.arr c.sink = st.regs 63 ∧
      (∀ j, j ≠ c.sink → out.arr j = st.arr j) ∧
      out.regs rPj = st.regs rPj + 1 ∧ out.regs rN = st.regs rN := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hzero1 : st.regs 1 = 0 := by simpa [rZero] using hzero
  have hsinkMod : c.sink % M = c.sink := Nat.mod_eq_of_lt hsinkM
  have hpjMod : (st.regs rPj + 1) % M = st.regs rPj + 1 :=
    Nat.mod_eq_of_lt hpjNextM
  have hpjMod8 : (st.regs 8 + 1) % M = st.regs 8 + 1 := by
    simpa [rPj] using hpjMod
  have hnMod7 : st.regs 7 % M = st.regs 7 :=
    Nat.mod_eq_of_lt (hword 7)
  simp [sieveInactiveSuffix, muxBody, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
    AState.writeArr, rZero, rN, rPj, hgate, hlast, hzero1, hsinkMod,
    hpjMod8, hnMod7, h1M]
  intro j hne heq
  exact (hne heq).elim

theorem sieveLastTest_nonlast (c : Cfg) (idx : Nat) (st : AState)
    (hpnM : c.pn < M) (hpjNe : st.regs rPj ≠ c.pn - 1) :
    (arun idx st (sieveLastTest c)).regs 64 = 0 := by
  have hlastM : c.pn - 1 < M := by omega
  have hlastMod : (c.pn - 1) % M = c.pn - 1 :=
    Nat.mod_eq_of_lt hlastM
  have hpjNe8 : st.regs 8 ≠ c.pn - 1 := by simpa [rPj] using hpjNe
  simp [sieveLastTest, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, rPj,
    hlastMod, hpjNe8]

/-- A complete active non-final-prime body refines one pure row step. Its
provisional code is deliberately stored only in the scratch sink. -/
theorem sieveBody_nonlast_model (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hpjNe : st.regs rPj ≠ c.pn - 1)
    (hprime : 0 < st.arr (st.regs rPj))
    (hpnM : c.pn < M) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) (hpjNextM : st.regs rPj + 1 < M)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let code := sieveCodeOf (sieveRowStep st).m (sieveRowStep st).par
      (sieveRowStep st).sqf
    let out := arun idx st c.sieveBody
    out.arr c.sink = code ∧
      (∀ j, j ≠ c.sink → out.arr j = st.arr j) ∧
      out.regs rPj = st.regs rPj + 1 ∧ out.regs rN = st.regs rN := by
  let pre29 := arun idx st (c.sieveBody.take 29)
  let pre30 := arun idx st (c.sieveBody.take 30)
  have hcode29 := sieveBody_prefix_code_model c idx st hgate hprime hword harr
  have hcode30 : pre30.regs 63 =
      sieveCodeOf (sieveRowStep st).m (sieveRowStep st).par
        (sieveRowStep st).sqf := by
    rw [show pre30 = arun idx pre29 (sieveLastTest c) by
      simp only [pre30, pre29, sieveBody_prefix_last_split, arun_append]]
    rw [show (arun idx pre29 (sieveLastTest c)).regs 63 = pre29.regs 63 from
      ArrayRegFrame.arun_frame idx 63 (sieveLastTest c) (by rfl) pre29]
    exact hcode29
  have hpj29 : pre29.regs rPj = st.regs rPj :=
    ArrayRegFrame.arun_frame idx rPj (c.sieveBody.take 29) (by rfl) st
  have hlast29 := sieveLastTest_nonlast c idx pre29 hpnM (by
    rw [hpj29]
    exact hpjNe)
  have hlast30 : pre30.regs 64 = 0 := by
    rw [show pre30 = arun idx pre29 (sieveLastTest c) by
      simp only [pre30, pre29, sieveBody_prefix_last_split, arun_append]]
    exact hlast29
  have hgate30 : pre30.regs 40 = 1 := by
    rw [show pre30.regs 40 = st.regs 40 from
      ArrayRegFrame.arun_frame idx 40 (c.sieveBody.take 30) (by rfl) st,
      hgate]
  have hzero30 : pre30.regs rZero = 0 := by
    rw [show pre30.regs rZero = st.regs rZero from
      ArrayRegFrame.arun_frame idx rZero (c.sieveBody.take 30) (by rfl) st,
      hzero]
  have hpj30 : pre30.regs rPj = st.regs rPj :=
    ArrayRegFrame.arun_frame idx rPj (c.sieveBody.take 30) (by rfl) st
  have hn30 : pre30.regs rN = st.regs rN :=
    ArrayRegFrame.arun_frame idx rN (c.sieveBody.take 30) (by rfl) st
  have hpreArr : pre30.arr = st.arr :=
    arun_store_free_arr idx (c.sieveBody.take 30) st (by rfl)
  have hpw := arun_word idx (c.sieveBody.take 30) st hword harr
  have hs := sieve_nonlast_suffix c idx pre30 hgate30 hlast30 hzero30
    hsinkM (by rw [hpj30]; exact hpjNextM) hpw.1
  rw [sieveBody_inactive_split, arun_append]
  change (arun idx pre30 (sieveInactiveSuffix c)).arr c.sink = _ ∧ _
  constructor
  · rw [hs.1, hcode30]
  constructor
  · intro j hj
    rw [hs.2.1 j hj, hpreArr]
  · exact ⟨hs.2.2.1.trans (congrArg (fun n => n + 1) hpj30),
      hs.2.2.2.trans hn30⟩

end LeanCompCert.Ports.CDEMAbelSieveStep

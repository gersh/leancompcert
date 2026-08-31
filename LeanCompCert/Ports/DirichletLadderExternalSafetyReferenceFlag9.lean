import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceDerived

/-! Historical instructions 129--138: the ninth reference flag.  The bound
`stat ≤ maxStat` is explicit: it is exactly what an accepting execution's
eighth flag establishes, and is not part of the external analytic evidence. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem and_one_eq_mod_two (x : Nat) : x &&& 1 = x % 2 := by
  rw [show 1 = 2 ^ 1 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem xor_bit_eq (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    a ^^^ b = if a != b then 1 else 0 := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> decide

theorem same_mul_xor_bit (same : Bool) (a b : Nat)
    (ha : a ≤ 1) (hb : b ≤ 1) :
    (if same then 1 else 0) * (a ^^^ b) =
      if same && a != b then 1 else 0 := by
  rw [xor_bit_eq a b ha hb]
  cases same <;> cases (a != b) <;> rfl

theorem bitCount_transWord_le (bits : Nat) :
    bitCount (transWord bits) ≤ 64 := by
  rw [bitCount_bytes _ (transWord_bit63_zero bits)]
  have h0 := popc8_le (byteAt (transWord bits) 0)
  have h1 := popc8_le (byteAt (transWord bits) 1)
  have h2 := popc8_le (byteAt (transWord bits) 2)
  have h3 := popc8_le (byteAt (transWord bits) 3)
  have h4 := popc8_le (byteAt (transWord bits) 4)
  have h5 := popc8_le (byteAt (transWord bits) 5)
  have h6 := popc8_le (byteAt (transWord bits) 6)
  have h7 := popc8_le (byteAt (transWord bits) 7)
  omega

theorem bitMoment_transWord_le (bits : Nat) :
    bitMoment (transWord bits) ≤ 2240 := by
  rw [bitMoment_bytes _ (transWord_bit63_zero bits)]
  have m0 := mom8_le (byteAt (transWord bits) 0)
  have m1 := mom8_le (byteAt (transWord bits) 1)
  have m2 := mom8_le (byteAt (transWord bits) 2)
  have m3 := mom8_le (byteAt (transWord bits) 3)
  have m4 := mom8_le (byteAt (transWord bits) 4)
  have m5 := mom8_le (byteAt (transWord bits) 5)
  have m6 := mom8_le (byteAt (transWord bits) 6)
  have m7 := mom8_le (byteAt (transWord bits) 7)
  have p1 := popc8_le (byteAt (transWord bits) 1)
  have p2 := popc8_le (byteAt (transWord bits) 2)
  have p3 := popc8_le (byteAt (transWord bits) 3)
  have p4 := popc8_le (byteAt (transWord bits) 4)
  have p5 := popc8_le (byteAt (transWord bits) 5)
  have p6 := popc8_le (byteAt (transWord bits) 6)
  have p7 := popc8_le (byteAt (transWord bits) 7)
  omega

def historicalFlag9 (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 129).take 10

theorem historicalFlag9_eq_source (c : Cfg) :
    historicalFlag9 c =
      [ bo 96 .band (.reg 26) (.lit 1)
      , bo 97 .lshr (.reg 26) (.lit 63)
      , bo 97 .band (.reg 97) (.lit 1)
      , bo 98 .bxor (.reg rPrevBit) (.reg 96)
      , bo 98 .mul (.reg 33) (.reg 98)
      , bo 99 .mul (.reg 27) (.lit 2)
      , bo 100 .add (.reg 77) (.reg 98)
      , bo 100 .add (.reg 100) (.reg 99)
      , bo 101 .ne (.reg 24) (.reg 100)
      , bo rViol .add (.reg rViol) (.reg 101) ] := by
  rfl

theorem historicalFlag9_result
    (c : Cfg) (idx n bits slots stat prevBit : Nat) (same : Bool)
    (s : AState)
    (hv : s.regs rViol = n) (hbits : s.regs 26 = bits)
    (hslots : s.regs 24 = slots) (hstat : s.regs 27 = stat)
    (hsame : s.regs 33 = if same then 1 else 0)
    (hprev : s.regs rPrevBit = prevBit)
    (htrI : s.regs 77 = bitCount (transWord bits))
    (hbitsWord : bits < M) (hprevBit : prevBit ≤ 1)
    (hstatBound : stat ≤ maxStat) (hNoWrap : n + 1 < M) :
    let fb := bits % 2
    let lb := (bits >>> 63) % 2
    let cross := if same && prevBit != fb then 1 else 0
    let derived := bitCount (transWord bits) + cross + 2 * stat
    let out := arun idx s (historicalFlag9 c)
    out.regs rViol = bump (slots != derived) n ∧
      out.regs 96 = fb ∧ out.regs 97 = lb ∧
      out.regs 98 = cross ∧ out.regs 100 = derived := by
  have hfb : bits % 2 ≤ 1 := by
    have := Nat.mod_lt bits (by decide : 0 < 2)
    omega
  have hnWord : n < M := by omega
  have hv0 : s.regs 0 = n := by simpa [rViol] using hv
  have hprev0 : s.regs 4 = prevBit := by simpa [rPrevBit] using hprev
  have hfbWord : bits % 2 < M := by
    exact Nat.lt_of_le_of_lt hfb (by simp [M])
  have hshift : bits >>> 63 < M := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hbitsWord
  have hlbWord : (bits >>> 63) % 2 < M := by
    have hmod := Nat.mod_lt (bits >>> 63) (by decide : 0 < 2)
    exact Nat.lt_trans hmod (by simp [M])
  have hcross :
      (if same then 1 else 0) * (prevBit ^^^ bits % 2) =
        if same && prevBit != bits % 2 then 1 else 0 :=
    same_mul_xor_bit same prevBit (bits % 2) hprevBit hfb
  have hcross' :
      (if same then 1 else 0) * (if prevBit = bits % 2 then 0 else 1) =
        if same && prevBit != bits % 2 then 1 else 0 := by
    calc
      _ = (if same then 1 else 0) * (prevBit ^^^ bits % 2) := by
        rw [xor_bit_eq prevBit (bits % 2) hprevBit hfb]
        by_cases h : prevBit = bits % 2 <;> simp [h]
      _ = _ := hcross
  have hxorWord : prevBit ^^^ bits % 2 < M := by
    rw [xor_bit_eq prevBit (bits % 2) hprevBit hfb]
    split <;> simp [M]
  have hcrossWord :
      (if same then 1 else 0) * (prevBit ^^^ bits % 2) < M := by
    rw [hcross]
    split <;> simp [M]
  have hderived :
      bitCount (transWord bits) +
          (if same && prevBit != bits % 2 then 1 else 0) + 2 * stat < M := by
    have hc := bitCount_transWord_le bits
    have hcrossLe : (if same && prevBit != bits % 2 then 1 else 0) ≤ 1 := by
      split <;> omega
    change stat ≤ 4 at hstatBound
    simp only [M]
    omega
  have hstatMul : stat * 2 < M := by
    change stat ≤ 4 at hstatBound
    simp only [M]
    omega
  have hpartial :
      bitCount (transWord bits) +
          (if same && prevBit != bits % 2 then 1 else 0) < M := by
    omega
  have hcrossPropWord :
      (if same = true ∧ ¬prevBit = bits % 2 then 1 else 0) < M := by
    split <;> simp [M]
  have hbool :
      (if (same && prevBit != bits % 2) = true then 1 else 0) =
        if same = true ∧ ¬prevBit = bits % 2 then 1 else 0 := by
    simp
  have hderivedProp :
      (bitCount (transWord bits) +
          (if same = true ∧ ¬prevBit = bits % 2 then 1 else 0) +
        stat * 2) < M := by
    simpa [Nat.mul_comm] using hderived
  simp [historicalFlag9_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hv0, hbits, hslots, hstat, hsame, hprev0, htrI,
    Nat.mod_eq_of_lt hbitsWord, Nat.mod_eq_of_lt one_lt_M,
    Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hfbWord,
    Nat.mod_eq_of_lt hxorWord, Nat.mod_eq_of_lt hcrossWord,
    and_one_eq_mod_two,
    xor_bit_eq prevBit (bits % 2) hprevBit hfb, hcross,
    Nat.mod_eq_of_lt hstatMul, Nat.mod_eq_of_lt hpartial,
    Nat.mod_eq_of_lt hderived, Nat.mod_eq_of_lt hNoWrap,
    bump, Nat.mul_comm, rViol, rPrevBit]
  simp only [Nat.mod_eq_of_lt (by decide : 63 < M),
    Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hfbWord,
    Nat.mod_eq_of_lt hlbWord, hcross']
  rw [hbool]
  rw [Nat.mod_eq_of_lt hcrossPropWord, Nat.mod_eq_of_lt hderivedProp]
  by_cases hc : slots =
      bitCount (transWord bits) +
        (if same = true ∧ ¬prevBit = bits % 2 then 1 else 0) + stat * 2
  · simp [hc, Nat.mod_eq_of_lt hnWord]
  · simp [hc, Nat.mod_eq_of_lt hNoWrap]

end LeanCompCert.Ports.DirichletLadderExternalSafety

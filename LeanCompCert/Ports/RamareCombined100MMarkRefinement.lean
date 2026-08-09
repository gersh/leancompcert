import LeanCompCert.Ports.RamareCombined100MShapeSieve
import LeanCompCert.Ports.RamareCombined100MSegModel

/-!
# Seven-plane marking refinement for the Ramaré 100-million sweep

This file is the refinement layer between the physical seven-plane array
program and `RamareCombined100MSeg.Cell`.  It is separate from the emitter so
the emitted instruction list remains stable while the loop invariant is built
in small, memory-bounded lemmas.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

/-- At a window boundary the cursor is reset to the first table prime and its
first multiple in the new window. -/
theorem Cfg.markResetBody_zero_run (c : Cfg) (k : Nat) (s : AState)
    (hround : s.regs rR = 0)
    (hp0 : c.table.headD 1 ≠ 0)
    (hp0M : c.table.headD 1 < M) :
    let p0 := c.table.headD 1
    let out := arun k s c.markResetBody
    out.regs rPi = 0 ∧ out.regs rPow = p0 ∧ out.regs rBase = p0 ∧
      out.regs rJ = (p0 - s.regs rW % p0) % p0 ∧
      out.regs rR = 0 ∧ out.regs rW = s.regs rW ∧ out.arr = s.arr := by
  have hround5 : s.regs 5 = 0 := by simpa [rR] using hround
  have hnotM : (1 + (M - 1)) % M = 0 := by
    have hM : 1 ≤ M := M_pos
    rw [show 1 + (M - 1) = M by omega, Nat.mod_self]
  have hp0mod : c.table.headD 1 % M = c.table.headD 1 :=
    Nat.mod_eq_of_lt hp0M
  have hrem : s.regs rW % c.table.headD 1 < c.table.headD 1 :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero hp0)
  have hsubM : c.table.headD 1 - s.regs rW % c.table.headD 1 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hp0M
  have hremWord : s.regs 6 % c.table.headD 1 < M := by
    simpa [rW] using Nat.lt_trans hrem hp0M
  have hremmodWord :
      (s.regs 6 % c.table.headD 1) % M =
        s.regs 6 % c.table.headD 1 := Nat.mod_eq_of_lt hremWord
  have hsubWord :
      (c.table.headD 1 + (M - s.regs 6 % c.table.headD 1)) % M =
        c.table.headD 1 - s.regs 6 % c.table.headD 1 := by
    have hle : s.regs 6 % c.table.headD 1 ≤ c.table.headD 1 := by
      simpa [rW] using Nat.le_of_lt hrem
    have hrew :
        c.table.headD 1 + (M - s.regs 6 % c.table.headD 1) =
          M + (c.table.headD 1 - s.regs 6 % c.table.headD 1) := by
      omega
    rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt]
    simpa [rW] using hsubM
  have hremM :
      (c.table.headD 1 - s.regs rW % c.table.headD 1) %
          c.table.headD 1 < M :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hp0))
      (Nat.le_of_lt hp0M)
  have hp0' : c.table.head?.getD 1 ≠ 0 := by simpa using hp0
  have hp0mod' : c.table.head?.getD 1 % M = c.table.head?.getD 1 := by
    simpa using hp0mod
  have hremM' : (c.table.head?.getD 1 - s.regs 6 %
      c.table.head?.getD 1) % c.table.head?.getD 1 < M := by
    simpa [rW] using hremM
  have hremmodWord' : s.regs 6 % c.table.head?.getD 1 % M =
      s.regs 6 % c.table.head?.getD 1 := by simpa using hremmodWord
  have hsubWord' : (c.table.head?.getD 1 +
      (M - s.regs 6 % c.table.head?.getD 1)) % M =
        c.table.head?.getD 1 - s.regs 6 % c.table.head?.getD 1 := by
    simpa using hsubWord
  simp [Cfg.markResetBody, arun, astep, AState.writeReg, sdest,
    sval, denoteOperand, denoteOp, hround5, hnotM, hp0', hp0mod',
    hremmodWord', hsubWord',
    Nat.mod_eq_of_lt hremM', rR, rW, rPi, rPow,
    rBase, rJ]

/-- Away from a window boundary the reset block preserves the entire
prime-power cursor. -/
theorem Cfg.markResetBody_nonzero_run (c : Cfg) (k : Nat) (s : AState)
    (hround : s.regs rR ≠ 0)
    (hPi : s.regs rPi < M) (hPow : s.regs rPow < M)
    (hBase : s.regs rBase < M) (hJ : s.regs rJ < M) :
    let out := arun k s c.markResetBody
    out.regs rPi = s.regs rPi ∧ out.regs rPow = s.regs rPow ∧
      out.regs rBase = s.regs rBase ∧ out.regs rJ = s.regs rJ ∧
      out.regs rR = s.regs rR ∧ out.regs rW = s.regs rW ∧
      out.arr = s.arr := by
  have hround5 : s.regs 5 ≠ 0 := by simpa [rR] using hround
  have hone : 1 % M = 1 := by decide
  have hPi2 : s.regs 2 % M = s.regs 2 := by
    exact Nat.mod_eq_of_lt (by simpa [rPi] using hPi)
  have hPow3 : s.regs 3 % M = s.regs 3 := by
    exact Nat.mod_eq_of_lt (by simpa [rPow] using hPow)
  have hBase7 : s.regs 7 % M = s.regs 7 := by
    exact Nat.mod_eq_of_lt (by simpa [rBase] using hBase)
  have hJ4 : s.regs 4 % M = s.regs 4 := by
    exact Nat.mod_eq_of_lt (by simpa [rJ] using hJ)
  simp [Cfg.markResetBody, arun, astep, AState.writeReg, sdest,
    sval, denoteOperand, denoteOp, hround5, hone, hPi2, hPow3, hBase7, hJ4,
    rR, rW, rPi, rPow, rBase, rJ]

/-- A live cursor selects the same offset in all seven planes.  These are the
addresses used by both the mark stores and the later classification loads. -/
theorem Cfg.markAddressBody_live_run (c : Cfg) (k : Nat) (s : AState)
    (hphase : s.regs 10 = 1) (hlive : s.regs rJ < c.segLen)
    (h0 : s.regs rJ < M)
    (h1 : s.regs rJ + c.segLen < M)
    (h2 : s.regs rJ + 2 * c.segLen < M)
    (h3 : s.regs rJ + 3 * c.segLen < M)
    (h4 : s.regs rJ + 4 * c.segLen < M)
    (h5 : s.regs rJ + 5 * c.segLen < M)
    (h6 : s.regs rJ + 6 * c.segLen < M) :
    let out := arun k s c.markAddressBody
    out.regs 24 = 1 ∧ out.regs 25 = 0 ∧
      out.regs 30 = s.regs rJ ∧
      out.regs 31 = s.regs rJ + c.segLen ∧
      out.regs 32 = s.regs rJ + 2 * c.segLen ∧
      out.regs 33 = s.regs rJ + 3 * c.segLen ∧
      out.regs 34 = s.regs rJ + 4 * c.segLen ∧
      out.regs 35 = s.regs rJ + 5 * c.segLen ∧
      out.regs 36 = s.regs rJ + 6 * c.segLen ∧
      out.regs rJ = s.regs rJ ∧ out.regs rBase = s.regs rBase ∧
      out.arr = s.arr := by
  have hlive4 : s.regs 4 < c.segLen := by simpa [rJ] using hlive
  have h04 : s.regs 4 < M := by simpa [rJ] using h0
  have h14 : s.regs 4 + c.segLen < M := by simpa [rJ] using h1
  have h24 : s.regs 4 + 2 * c.segLen < M := by simpa [rJ] using h2
  have h34 : s.regs 4 + 3 * c.segLen < M := by simpa [rJ] using h3
  have h44 : s.regs 4 + 4 * c.segLen < M := by simpa [rJ] using h4
  have h54 : s.regs 4 + 5 * c.segLen < M := by simpa [rJ] using h5
  have h64 : s.regs 4 + 6 * c.segLen < M := by simpa [rJ] using h6
  have hL : c.segLen < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h1
  have h2L : 2 * c.segLen < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h2
  have h3L : 3 * c.segLen < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h3
  have h4L : 4 * c.segLen < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h4
  have h5L : 5 * c.segLen < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h5
  have h6L : 6 * c.segLen < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h6
  have hone : 1 % M = 1 := by decide
  have hnotM : (1 + (M - 1)) % M = 0 := by
    have hM : 1 ≤ M := M_pos
    rw [show 1 + (M - 1) = M by omega, Nat.mod_self]
  simp [Cfg.markAddressBody, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, hphase, hlive4, hone, hnotM,
    Nat.mod_eq_of_lt h04, Nat.mod_eq_of_lt h14, Nat.mod_eq_of_lt h24,
    Nat.mod_eq_of_lt h34, Nat.mod_eq_of_lt h44, Nat.mod_eq_of_lt h54,
    Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt h2L,
    Nat.mod_eq_of_lt h3L, Nat.mod_eq_of_lt h4L, Nat.mod_eq_of_lt h5L,
    Nat.mod_eq_of_lt h6L, rJ, rBase]

/-- The mark loads read the seven selected plane cells and preserve their
addresses. -/
theorem Cfg.markLoadBody_run (k : Nat) (s : AState) :
    let out := arun k s Cfg.markLoadBody
    out.regs 40 = s.arr (s.regs 30) ∧
      out.regs 41 = s.arr (s.regs 31) ∧
      out.regs 42 = s.arr (s.regs 32) ∧
      out.regs 43 = s.arr (s.regs 33) ∧
      out.regs 44 = s.arr (s.regs 34) ∧
      out.regs 45 = s.arr (s.regs 35) ∧
      out.regs 46 = s.arr (s.regs 36) ∧
      out.regs 30 = s.regs 30 ∧ out.regs 31 = s.regs 31 ∧
      out.regs 32 = s.regs 32 ∧ out.regs 33 = s.regs 33 ∧
      out.regs 34 = s.regs 34 ∧ out.regs 35 = s.regs 35 ∧
      out.regs 36 = s.regs 36 ∧ out.arr = s.arr := by
  simp [Cfg.markLoadBody, arun, astep, AState.writeReg]

/-- One prime-power hit multiplies the normalized all-product cell by its
prime base and writes that exact value back to plane zero. -/
theorem Cfg.markAllProductBody_run (k : Nat) (s : AState)
    (hnorm : nonzeroProduct (s.regs 40) < M)
    (hprod : nonzeroProduct (s.regs 40) * s.regs rBase < M) :
    let value := nonzeroProduct (s.regs 40) * s.regs rBase
    let out := arun k s Cfg.markAllProductBody
    out.regs 47 = zeroBit (s.regs 40) ∧
      out.regs 48 = nonzeroProduct (s.regs 40) ∧
      out.regs 49 = value ∧
      out.arr = (s.writeArr (s.regs 30) value).arr ∧
      out.regs 30 = s.regs 30 ∧ out.regs 40 = s.regs 40 ∧
      out.regs rBase = s.regs rBase := by
  have hnormN : nonzeroProduct (s.regs 40) < 18446744073709551616 := by
    simpa [M] using hnorm
  have hprodN : nonzeroProduct (s.regs 40) * s.regs rBase <
      18446744073709551616 := by simpa [M] using hprod
  have hnormPos : 0 < nonzeroProduct (s.regs 40) := by
    by_cases hz : s.regs 40 = 0
    · simp [nonzeroProduct, zeroBit, hz]
    · simpa [nonzeroProduct, zeroBit, hz] using Nat.pos_of_ne_zero hz
  have hbase : s.regs rBase < M :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hnormPos) hprod
  have hbase7N : s.regs 7 < 18446744073709551616 := by
    simpa [rBase, M] using hbase
  have hbaseModN : s.regs 7 % 18446744073709551616 = s.regs 7 :=
    Nat.mod_eq_of_lt hbase7N
  by_cases hz : s.regs 40 = 0
  · simp [Cfg.markAllProductBody, arun, astep, AState.writeReg,
      AState.writeArr, sdest, sval, denoteOperand, denoteOp, nonzeroProduct,
      zeroBit, hz, hbaseModN, rBase, M]
  · have h40N : s.regs 40 < 18446744073709551616 := by
      simpa [nonzeroProduct, zeroBit, hz] using hnormN
    have hmulN : s.regs 40 * s.regs 7 < 18446744073709551616 := by
      simpa [nonzeroProduct, zeroBit, hz, rBase] using hprodN
    have hmulModN :
        (s.regs 40 * s.regs 7) % 18446744073709551616 =
          s.regs 40 * s.regs 7 := Nat.mod_eq_of_lt hmulN
    simp [Cfg.markAllProductBody, arun, astep, AState.writeReg,
      AState.writeArr, sdest, sval, denoteOperand, denoteOp, nonzeroProduct,
      zeroBit, hz, h40N, hmulModN, rBase, M]

/-- Equality bit used by the logical account of a prime-power hit. -/
def eqBit (x y : Nat) : Nat := if x = y then 1 else 0

/-- Install the first prime exactly on the first power of a new base when the
first-prime plane is still empty. -/
def installP (pow base p : Nat) : Nat := eqBit pow base * zeroBit p

/-- A power hit belongs to the first recorded prime either when it installs
that prime or when the base is already recorded there. -/
def hitP (pow base p : Nat) : Nat := installP pow base p + eqBit base p

def nextP (pow base p : Nat) : Nat :=
  installP pow base p * base + (1 - installP pow base p) * p

/-- The first-prime selector block implements `installP`, `hitP`, and
`nextP` exactly and stores the selected base in plane one. -/
theorem Cfg.markFirstSelectBody_run (k : Nat) (s : AState)
    (hbase0 : s.regs rBase ≠ 0)
    (hbase : s.regs rBase < M) (hp : s.regs 41 < M) :
    let install := installP (s.regs rPow) (s.regs rBase) (s.regs 41)
    let hit := hitP (s.regs rPow) (s.regs rBase) (s.regs 41)
    let value := nextP (s.regs rPow) (s.regs rBase) (s.regs 41)
    let out := arun k s Cfg.markFirstSelectBody
    out.regs 50 = eqBit (s.regs rPow) (s.regs rBase) ∧
      out.regs 51 = zeroBit (s.regs 41) ∧
      out.regs 52 = install ∧ out.regs 53 = eqBit (s.regs rBase) (s.regs 41) ∧
      out.regs 54 = hit ∧ out.regs 58 = value ∧
      out.arr = (s.writeArr (s.regs 31) value).arr ∧
      out.regs 31 = s.regs 31 ∧ out.regs 42 = s.regs 42 ∧
      out.regs 43 = s.regs 43 ∧ out.regs rPow = s.regs rPow ∧
      out.regs rBase = s.regs rBase := by
  have hbase7 : s.regs 7 ≠ 0 := by simpa [rBase] using hbase0
  have hbase7M : s.regs 7 < 18446744073709551616 := by
    simpa [rBase, M] using hbase
  have hpN : s.regs 41 < 18446744073709551616 := by simpa [M] using hp
  have hbaseMod : s.regs 7 % 18446744073709551616 = s.regs 7 :=
    Nat.mod_eq_of_lt hbase7M
  have hpMod : s.regs 41 % 18446744073709551616 = s.regs 41 :=
    Nat.mod_eq_of_lt hpN
  by_cases hpow : s.regs rPow = s.regs rBase
  · have hpow37 : s.regs 3 = s.regs 7 := by simpa [rPow, rBase] using hpow
    by_cases hp0 : s.regs 41 = 0
    · simp [Cfg.markFirstSelectBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp, eqBit,
        installP, hitP, nextP, zeroBit, hpow37, hp0, hbase7,
        hbaseMod, rPow, rBase, M]
    · by_cases hsame : s.regs rBase = s.regs 41
      · have hsame7 : s.regs 7 = s.regs 41 := by
          simpa [rBase] using hsame
        simp [Cfg.markFirstSelectBody, arun, astep, AState.writeReg,
          AState.writeArr, sdest, sval, denoteOperand, denoteOp, eqBit,
          installP, hitP, nextP, zeroBit, hpow37, hp0, hsame7,
          hpMod, rPow, rBase, M]
      · have hsame7 : s.regs 7 ≠ s.regs 41 := by
          simpa [rBase] using hsame
        simp [Cfg.markFirstSelectBody, arun, astep, AState.writeReg,
          AState.writeArr, sdest, sval, denoteOperand, denoteOp, eqBit,
          installP, hitP, nextP, zeroBit, hpow37, hp0, hsame7,
          hpMod, rPow, rBase, M]
  · have hpow37 : s.regs 3 ≠ s.regs 7 := by simpa [rPow, rBase] using hpow
    by_cases hp0 : s.regs 41 = 0
    · simp [Cfg.markFirstSelectBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp, eqBit,
        installP, hitP, nextP, zeroBit, hpow37, hp0, hbase7,
        rPow, rBase, M]
    · by_cases hsame : s.regs rBase = s.regs 41
      · have hsame7 : s.regs 7 = s.regs 41 := by
          simpa [rBase] using hsame
        simp [Cfg.markFirstSelectBody, arun, astep, AState.writeReg,
          AState.writeArr, sdest, sval, denoteOperand, denoteOp, eqBit,
          installP, hitP, nextP, zeroBit, hp0, hsame7,
          hpMod, rPow, rBase, M]
      · have hsame7 : s.regs 7 ≠ s.regs 41 := by
          simpa [rBase] using hsame
        simp [Cfg.markFirstSelectBody, arun, astep, AState.writeReg,
          AState.writeArr, sdest, sval, denoteOperand, denoteOp, eqBit,
          installP, hitP, nextP, zeroBit, hpow37, hp0, hsame7,
          hpMod, rPow, rBase, M]

/-- The first exponent plane advances by the exact first-prime hit bit. -/
theorem Cfg.markFirstExponentBody_run (k : Nat) (s : AState)
    (hsum : s.regs 42 + s.regs 54 < M) :
    let value := s.regs 42 + s.regs 54
    let out := arun k s Cfg.markFirstExponentBody
    out.regs 59 = value ∧
      out.arr = (s.writeArr (s.regs 32) value).arr ∧
      out.regs 32 = s.regs 32 ∧ out.regs 42 = s.regs 42 ∧
      out.regs 43 = s.regs 43 ∧ out.regs 54 = s.regs 54 := by
  have hsumN : s.regs 42 + s.regs 54 < 18446744073709551616 := by
    simpa [M] using hsum
  have hsumMod :
      (s.regs 42 + s.regs 54) % 18446744073709551616 =
        s.regs 42 + s.regs 54 := Nat.mod_eq_of_lt hsumN
  simp [Cfg.markFirstExponentBody, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, denoteOp, hsumMod, M]

/-- Logical update of one exact prime-power product plane. -/
def nextPowerProduct (hit raw base : Nat) : Nat :=
  hit * (nonzeroProduct raw * base) + (1 - hit) * raw

theorem installP_le_one (pow base p : Nat) : installP pow base p ≤ 1 := by
  simp only [installP, eqBit, zeroBit]
  split <;> split <;> omega

theorem hitP_le_one (pow base p : Nat) (hbase : base ≠ 0) :
    hitP pow base p ≤ 1 := by
  simp only [hitP, installP, eqBit, zeroBit]
  split <;> split <;> split <;> simp_all

/-- The first exact-product plane is extended precisely on first-prime hits. -/
theorem Cfg.markFirstProductBody_run (k : Nat) (s : AState)
    (hhit : s.regs 54 ≤ 1)
    (hnorm : nonzeroProduct (s.regs 43) < M)
    (hmul : nonzeroProduct (s.regs 43) * s.regs rBase < M) :
    let value := nextPowerProduct (s.regs 54) (s.regs 43) (s.regs rBase)
    let out := arun k s Cfg.markFirstProductBody
    out.regs 60 = zeroBit (s.regs 43) ∧
      out.regs 61 = nonzeroProduct (s.regs 43) ∧
      out.regs 62 = nonzeroProduct (s.regs 43) * s.regs rBase ∧
      out.regs 66 = value ∧
      out.arr = (s.writeArr (s.regs 33) value).arr ∧
      out.regs 33 = s.regs 33 ∧ out.regs 43 = s.regs 43 ∧
      out.regs 54 = s.regs 54 ∧ out.regs rBase = s.regs rBase := by
  have hnormN : nonzeroProduct (s.regs 43) < 18446744073709551616 := by
    simpa [M] using hnorm
  have hmulN : nonzeroProduct (s.regs 43) * s.regs rBase <
      18446744073709551616 := by simpa [M] using hmul
  have hraw : s.regs 43 < M := by
    by_cases hz : s.regs 43 = 0
    · simp [hz, M]
    · simpa [nonzeroProduct, zeroBit, hz] using hnorm
  have hrawN : s.regs 43 < 18446744073709551616 := by
    simpa [M] using hraw
  have hrawMod : s.regs 43 % 18446744073709551616 = s.regs 43 :=
    Nat.mod_eq_of_lt hrawN
  have hnormPos : 0 < nonzeroProduct (s.regs 43) := by
    by_cases hz : s.regs 43 = 0
    · simp [nonzeroProduct, zeroBit, hz]
    · simpa [nonzeroProduct, zeroBit, hz] using Nat.pos_of_ne_zero hz
  have hbaseM : s.regs rBase < M :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hnormPos) hmul
  have hbase7N : s.regs 7 < 18446744073709551616 := by
    simpa [rBase, M] using hbaseM
  have hbaseMod : s.regs 7 % 18446744073709551616 = s.regs 7 :=
    Nat.mod_eq_of_lt hbase7N
  have hmul7N : nonzeroProduct (s.regs 43) * s.regs 7 <
      18446744073709551616 := by simpa [rBase] using hmulN
  by_cases hhit0 : s.regs 54 = 0
  · by_cases hz : s.regs 43 = 0
    · simp [Cfg.markFirstProductBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp,
        nextPowerProduct, nonzeroProduct, zeroBit, hhit0, hz,
        hbaseMod, rBase, M]
    · have h43N : s.regs 43 < 18446744073709551616 := hrawN
      have hmulRawN : s.regs 43 * s.regs 7 < 18446744073709551616 := by
        simpa [nonzeroProduct, zeroBit, hz] using hmul7N
      have hmulRawMod :
          (s.regs 43 * s.regs 7) % 18446744073709551616 =
            s.regs 43 * s.regs 7 := Nat.mod_eq_of_lt hmulRawN
      simp [Cfg.markFirstProductBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp,
        nextPowerProduct, nonzeroProduct, zeroBit, hhit0, hz,
        hrawMod, hmulRawMod, rBase, M]
  · have hhit1 : s.regs 54 = 1 := by omega
    by_cases hz : s.regs 43 = 0
    · simp [Cfg.markFirstProductBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp,
        nextPowerProduct, nonzeroProduct, zeroBit, hhit1, hz,
        hbaseMod, rBase, M]
    · have h43N : s.regs 43 < 18446744073709551616 := hrawN
      have hmulRawN : s.regs 43 * s.regs 7 < 18446744073709551616 := by
        simpa [nonzeroProduct, zeroBit, hz] using hmul7N
      have hmulRawMod :
          (s.regs 43 * s.regs 7) % 18446744073709551616 =
            s.regs 43 * s.regs 7 := Nat.mod_eq_of_lt hmulRawN
      simp [Cfg.markFirstProductBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp,
        nextPowerProduct, nonzeroProduct, zeroBit, hhit1, hz,
        h43N, hmulRawMod, rBase, M]

/-- The three first-prime blocks compose without normalizing their combined
instruction stream.  The result records the exact three physical writes. -/
theorem Cfg.markFirstBody_run (k : Nat) (s : AState)
    (hbase0 : s.regs rBase ≠ 0)
    (hbase : s.regs rBase < M) (hp : s.regs 41 < M)
    (hpe : s.regs 42 + hitP (s.regs rPow) (s.regs rBase) (s.regs 41) < M)
    (hpp : nonzeroProduct (s.regs 43) < M)
    (hppMul : nonzeroProduct (s.regs 43) * s.regs rBase < M) :
    let hit := hitP (s.regs rPow) (s.regs rBase) (s.regs 41)
    let p := nextP (s.regs rPow) (s.regs rBase) (s.regs 41)
    let pe := s.regs 42 + hit
    let pp := nextPowerProduct hit (s.regs 43) (s.regs rBase)
    let out := arun k s Cfg.markFirstBody
    out.regs 50 = eqBit (s.regs rPow) (s.regs rBase) ∧
      out.regs 54 = hit ∧ out.regs 58 = p ∧ out.regs 59 = pe ∧
      out.regs 66 = pp ∧
      out.arr = (((s.writeArr (s.regs 31) p).writeArr
        (s.regs 32) pe).writeArr (s.regs 33) pp).arr ∧
      out.regs 41 = s.regs 41 ∧ out.regs 42 = s.regs 42 ∧
      out.regs 43 = s.regs 43 ∧ out.regs 44 = s.regs 44 ∧
      out.regs 45 = s.regs 45 ∧ out.regs 46 = s.regs 46 ∧
      out.regs 31 = s.regs 31 ∧ out.regs 32 = s.regs 32 ∧
      out.regs 33 = s.regs 33 ∧ out.regs 34 = s.regs 34 ∧
      out.regs 35 = s.regs 35 ∧ out.regs 36 = s.regs 36 ∧
      out.regs rPow = s.regs rPow ∧ out.regs rBase = s.regs rBase := by
  let s1 := arun k s Cfg.markFirstSelectBody
  let s2 := arun k s1 Cfg.markFirstExponentBody
  have hsel := Cfg.markFirstSelectBody_run k s hbase0 hbase hp
  dsimp only at hsel
  rcases hsel with
    ⟨h50, _h51, _h52, _h53, h54, h58, harr1, h31, h42, h43,
      hpow, hbase'⟩
  have harr1' : s1.arr =
      (s.writeArr (s.regs 31)
        (nextP (s.regs rPow) (s.regs rBase) (s.regs 41))).arr := harr1
  have frame1 (r : Nat) (h : writes r Cfg.markFirstSelectBody = false) :
      s1.regs r = s.regs r := by
    exact arun_frame k r Cfg.markFirstSelectBody h s
  have h32 : s1.regs 32 = s.regs 32 := frame1 32 (by decide)
  have h33 : s1.regs 33 = s.regs 33 := frame1 33 (by decide)
  have h44 : s1.regs 44 = s.regs 44 := frame1 44 (by decide)
  have h45 : s1.regs 45 = s.regs 45 := frame1 45 (by decide)
  have h46 : s1.regs 46 = s.regs 46 := frame1 46 (by decide)
  have h34 : s1.regs 34 = s.regs 34 := frame1 34 (by decide)
  have h35 : s1.regs 35 = s.regs 35 := frame1 35 (by decide)
  have h36 : s1.regs 36 = s.regs 36 := frame1 36 (by decide)
  have hexp := Cfg.markFirstExponentBody_run k s1 (by
    rw [h42, h54]
    exact hpe)
  dsimp only at hexp
  rcases hexp with ⟨h59, harr2, h32', h42', h43', h54'⟩
  have harr2' := harr2
  simp only [AState.writeArr] at harr1' harr2'
  rw [h32, h42, h54, harr1'] at harr2'
  have frame2 (r : Nat)
      (h : writes r Cfg.markFirstExponentBody = false) :
      s2.regs r = s1.regs r := by
    exact arun_frame k r Cfg.markFirstExponentBody h s1
  have h33' : s2.regs 33 = s1.regs 33 := frame2 33 (by decide)
  have hbase2 : s2.regs rBase = s1.regs rBase := frame2 rBase (by decide)
  have hprod := Cfg.markFirstProductBody_run k s2 (by
      rw [h54', h54]
      exact hitP_le_one _ _ _ hbase0) (by
      rw [h43', h43]
      exact hpp) (by
      rw [h43', h43, hbase2, hbase']
      exact hppMul)
  dsimp only at hprod
  rcases hprod with
    ⟨_h60, _h61, _h62, h66, harr3, h33'', h43'', h54'', hbase''⟩
  have frame3 (r : Nat)
      (h : writes r Cfg.markFirstProductBody = false) :
      (arun k s2 Cfg.markFirstProductBody).regs r = s2.regs r := by
    exact arun_frame k r Cfg.markFirstProductBody h s2
  simp only [Cfg.markFirstBody, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (frame3 50 (by decide)).trans ((frame2 50 (by decide)).trans h50)
  · exact h54''.trans (h54'.trans h54)
  · exact (frame3 58 (by decide)).trans ((frame2 58 (by decide)).trans h58)
  · exact (frame3 59 (by decide)).trans
      (h59.trans (congrArg (s.regs 42 + ·) h54))
  · rw [h54', h54, h43', h43, hbase2, hbase'] at h66
    exact h66
  · simp only [AState.writeArr] at harr3 ⊢
    rw [h33', h33, h54', h54, h43', h43, hbase2, hbase', harr2'] at harr3
    exact harr3
  · exact (frame3 41 (by decide)).trans ((frame2 41 (by decide)).trans
      (frame1 41 (by decide)))
  · exact (frame3 42 (by decide)).trans (h42'.trans h42)
  · exact h43''.trans (h43'.trans h43)
  · exact (frame3 44 (by decide)).trans ((frame2 44 (by decide)).trans h44)
  · exact (frame3 45 (by decide)).trans ((frame2 45 (by decide)).trans h45)
  · exact (frame3 46 (by decide)).trans ((frame2 46 (by decide)).trans h46)
  · exact (frame3 31 (by decide)).trans ((frame2 31 (by decide)).trans h31)
  · exact (frame3 32 (by decide)).trans (h32'.trans h32)
  · exact h33''.trans (h33'.trans h33)
  · exact (frame3 34 (by decide)).trans ((frame2 34 (by decide)).trans h34)
  · exact (frame3 35 (by decide)).trans ((frame2 35 (by decide)).trans h35)
  · exact (frame3 36 (by decide)).trans ((frame2 36 (by decide)).trans h36)
  · exact (frame3 rPow (by decide)).trans ((frame2 rPow (by decide)).trans hpow)
  · exact hbase''.trans (hbase2.trans hbase')

/-- Install the second prime exactly on the first power of a new base once a
first prime exists and the second-prime plane is still empty. -/
def installQ (pow base p q : Nat) : Nat :=
  eqBit pow base * nonzeroBit p * zeroBit q

def hitQ (pow base p q : Nat) : Nat :=
  installQ pow base p q + eqBit base q

def nextQ (pow base p q : Nat) : Nat :=
  installQ pow base p q * base + (1 - installQ pow base p q) * q

theorem installQ_le_one (pow base p q : Nat) : installQ pow base p q ≤ 1 := by
  simp only [installQ, eqBit, nonzeroBit, zeroBit]
  split <;> split <;> split <;> omega

theorem hitQ_le_one (pow base p q : Nat) (hbase : base ≠ 0) :
    hitQ pow base p q ≤ 1 := by
  simp only [hitQ, installQ, eqBit, nonzeroBit, zeroBit]
  split <;> split <;> split <;> split <;> simp_all

/-- The second-prime flag block implements `installQ` and `hitQ` exactly. -/
theorem Cfg.markSecondFlagsBody_run (k : Nat) (s : AState)
    (hfirst : s.regs 50 = eqBit (s.regs rPow) (s.regs rBase)) :
    let install := installQ (s.regs rPow) (s.regs rBase)
      (s.regs 41) (s.regs 44)
    let hit := hitQ (s.regs rPow) (s.regs rBase)
      (s.regs 41) (s.regs 44)
    let out := arun k s Cfg.markSecondFlagsBody
    out.regs 67 = nonzeroBit (s.regs 41) ∧
      out.regs 68 = zeroBit (s.regs 44) ∧
      out.regs 69 = eqBit (s.regs rPow) (s.regs rBase) *
        nonzeroBit (s.regs 41) ∧
      out.regs 70 = install ∧
      out.regs 71 = eqBit (s.regs rBase) (s.regs 44) ∧
      out.regs 72 = hit ∧ out.regs 34 = s.regs 34 ∧
      out.regs 44 = s.regs 44 ∧ out.regs rPow = s.regs rPow ∧
      out.regs rBase = s.regs rBase ∧ out.arr = s.arr := by
  have hfirst' := hfirst
  simp only [eqBit, rPow, rBase] at hfirst'
  have hzero7M : (if s.regs 7 = 0 then 1 else 0) <
      18446744073709551616 := by split <;> omega
  have hzero7SuccM : 1 + (if s.regs 7 = 0 then 1 else 0) <
      18446744073709551616 := by split <;> omega
  have hzero3M : (if s.regs 3 = 0 then 1 else 0) <
      18446744073709551616 := by split <;> omega
  have hzero3SuccM : (if s.regs 3 = 0 then 1 else 0) + 1 <
      18446744073709551616 := by split <;> omega
  have heq344M : (if s.regs 3 = s.regs 44 then 1 else 0) <
      18446744073709551616 := by split <;> omega
  by_cases hpow : s.regs 3 = s.regs 7 <;>
    by_cases hp0 : s.regs 41 = 0 <;>
      by_cases hq0 : s.regs 44 = 0 <;>
        by_cases hsame : s.regs 7 = s.regs 44 <;>
          simp [Cfg.markSecondFlagsBody, arun, astep, AState.writeReg,
            sdest, sval, denoteOperand, denoteOp, installQ, hitQ, eqBit,
            nonzeroBit, zeroBit, hfirst', hzero7M, hzero7SuccM, hzero3M,
            hzero3SuccM, heq344M, hpow, hp0, hq0, hsame, rPow, rBase, M]

/-- Commit an already computed second-prime installation bit. -/
theorem Cfg.markSecondCommitBody_run (k : Nat) (s : AState)
    (hinstall : s.regs 70 ≤ 1)
    (hbase : s.regs rBase < M) (hq : s.regs 44 < M) :
    let value := s.regs 70 * s.regs rBase + (1 - s.regs 70) * s.regs 44
    let out := arun k s Cfg.markSecondCommitBody
    out.regs 73 = 1 - s.regs 70 ∧
      out.regs 74 = s.regs 70 * s.regs rBase ∧
      out.regs 75 = (1 - s.regs 70) * s.regs 44 ∧
      out.regs 76 = value ∧
      out.arr = (s.writeArr (s.regs 34) value).arr ∧
      out.regs 34 = s.regs 34 ∧ out.regs 44 = s.regs 44 ∧
      out.regs 70 = s.regs 70 ∧ out.regs rBase = s.regs rBase := by
  have hbase7N : s.regs 7 < 18446744073709551616 := by
    simpa [rBase, M] using hbase
  have hqN : s.regs 44 < 18446744073709551616 := by simpa [M] using hq
  have hbaseMod : s.regs 7 % 18446744073709551616 = s.regs 7 :=
    Nat.mod_eq_of_lt hbase7N
  have hqMod : s.regs 44 % 18446744073709551616 = s.regs 44 :=
    Nat.mod_eq_of_lt hqN
  by_cases hi : s.regs 70 = 0
  · simp [Cfg.markSecondCommitBody, arun, astep, AState.writeReg,
      AState.writeArr, sdest, sval, denoteOperand, denoteOp, hi, hqMod,
      rBase, M]
  · have hi1 : s.regs 70 = 1 := by omega
    simp [Cfg.markSecondCommitBody, arun, astep, AState.writeReg,
      AState.writeArr, sdest, sval, denoteOperand, denoteOp, hi1,
      hbaseMod, rBase, M]

/-- The second exponent plane advances by the exact second-prime hit bit. -/
theorem Cfg.markSecondExponentBody_run (k : Nat) (s : AState)
    (hsum : s.regs 45 + s.regs 72 < M) :
    let value := s.regs 45 + s.regs 72
    let out := arun k s Cfg.markSecondExponentBody
    out.regs 77 = value ∧
      out.arr = (s.writeArr (s.regs 35) value).arr ∧
      out.regs 35 = s.regs 35 ∧ out.regs 45 = s.regs 45 ∧
      out.regs 46 = s.regs 46 ∧ out.regs 72 = s.regs 72 := by
  have hsumN : s.regs 45 + s.regs 72 < 18446744073709551616 := by
    simpa [M] using hsum
  have hsumMod :
      (s.regs 45 + s.regs 72) % 18446744073709551616 =
        s.regs 45 + s.regs 72 := Nat.mod_eq_of_lt hsumN
  simp [Cfg.markSecondExponentBody, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, denoteOp, hsumMod, M]

/-- The second exact-product plane is extended precisely on second-prime
hits. -/
theorem Cfg.markSecondProductBody_run (k : Nat) (s : AState)
    (hhit : s.regs 72 ≤ 1)
    (hnorm : nonzeroProduct (s.regs 46) < M)
    (hmul : nonzeroProduct (s.regs 46) * s.regs rBase < M) :
    let value := nextPowerProduct (s.regs 72) (s.regs 46) (s.regs rBase)
    let out := arun k s Cfg.markSecondProductBody
    out.regs 78 = zeroBit (s.regs 46) ∧
      out.regs 79 = nonzeroProduct (s.regs 46) ∧
      out.regs 80 = nonzeroProduct (s.regs 46) * s.regs rBase ∧
      out.regs 84 = value ∧
      out.arr = (s.writeArr (s.regs 36) value).arr ∧
      out.regs 36 = s.regs 36 ∧ out.regs 46 = s.regs 46 ∧
      out.regs 72 = s.regs 72 ∧ out.regs rBase = s.regs rBase := by
  have hnormN : nonzeroProduct (s.regs 46) < 18446744073709551616 := by
    simpa [M] using hnorm
  have hmulN : nonzeroProduct (s.regs 46) * s.regs rBase <
      18446744073709551616 := by simpa [M] using hmul
  have hraw : s.regs 46 < M := by
    by_cases hz : s.regs 46 = 0
    · simp [hz, M]
    · simpa [nonzeroProduct, zeroBit, hz] using hnorm
  have hrawN : s.regs 46 < 18446744073709551616 := by
    simpa [M] using hraw
  have hrawMod : s.regs 46 % 18446744073709551616 = s.regs 46 :=
    Nat.mod_eq_of_lt hrawN
  have hnormPos : 0 < nonzeroProduct (s.regs 46) := by
    by_cases hz : s.regs 46 = 0
    · simp [nonzeroProduct, zeroBit, hz]
    · simpa [nonzeroProduct, zeroBit, hz] using Nat.pos_of_ne_zero hz
  have hbaseM : s.regs rBase < M :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hnormPos) hmul
  have hbase7N : s.regs 7 < 18446744073709551616 := by
    simpa [rBase, M] using hbaseM
  have hbaseMod : s.regs 7 % 18446744073709551616 = s.regs 7 :=
    Nat.mod_eq_of_lt hbase7N
  have hmul7N : nonzeroProduct (s.regs 46) * s.regs 7 <
      18446744073709551616 := by simpa [rBase] using hmulN
  by_cases hhit0 : s.regs 72 = 0
  · by_cases hz : s.regs 46 = 0
    · simp [Cfg.markSecondProductBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp,
        nextPowerProduct, nonzeroProduct, zeroBit, hhit0, hz,
        hbaseMod, rBase, M]
    · have hmulRawN : s.regs 46 * s.regs 7 < 18446744073709551616 := by
        simpa [nonzeroProduct, zeroBit, hz] using hmul7N
      have hmulRawMod :
          (s.regs 46 * s.regs 7) % 18446744073709551616 =
            s.regs 46 * s.regs 7 := Nat.mod_eq_of_lt hmulRawN
      simp [Cfg.markSecondProductBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp,
        nextPowerProduct, nonzeroProduct, zeroBit, hhit0, hz,
        hrawMod, hmulRawMod, rBase, M]
  · have hhit1 : s.regs 72 = 1 := by omega
    by_cases hz : s.regs 46 = 0
    · simp [Cfg.markSecondProductBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp,
        nextPowerProduct, nonzeroProduct, zeroBit, hhit1, hz,
        hbaseMod, rBase, M]
    · have h46N : s.regs 46 < 18446744073709551616 := hrawN
      have hmulRawN : s.regs 46 * s.regs 7 < 18446744073709551616 := by
        simpa [nonzeroProduct, zeroBit, hz] using hmul7N
      have hmulRawMod :
          (s.regs 46 * s.regs 7) % 18446744073709551616 =
            s.regs 46 * s.regs 7 := Nat.mod_eq_of_lt hmulRawN
      simp [Cfg.markSecondProductBody, arun, astep, AState.writeReg,
        AState.writeArr, sdest, sval, denoteOperand, denoteOp,
        nextPowerProduct, nonzeroProduct, zeroBit, hhit1, hz,
        h46N, hmulRawMod, rBase, M]

/-- The four second-prime blocks compose from their small exact proofs and
record the exact three physical writes. -/
theorem Cfg.markSecondBody_run (k : Nat) (s : AState)
    (hfirst : s.regs 50 = eqBit (s.regs rPow) (s.regs rBase))
    (hbase0 : s.regs rBase ≠ 0)
    (hbase : s.regs rBase < M) (hq : s.regs 44 < M)
    (hqe : s.regs 45 + hitQ (s.regs rPow) (s.regs rBase)
      (s.regs 41) (s.regs 44) < M)
    (hqpp : nonzeroProduct (s.regs 46) < M)
    (hqppMul : nonzeroProduct (s.regs 46) * s.regs rBase < M) :
    let install := installQ (s.regs rPow) (s.regs rBase)
      (s.regs 41) (s.regs 44)
    let hit := hitQ (s.regs rPow) (s.regs rBase)
      (s.regs 41) (s.regs 44)
    let q := nextQ (s.regs rPow) (s.regs rBase)
      (s.regs 41) (s.regs 44)
    let qe := s.regs 45 + hit
    let qp := nextPowerProduct hit (s.regs 46) (s.regs rBase)
    let out := arun k s Cfg.markSecondBody
    out.regs 70 = install ∧ out.regs 72 = hit ∧
      out.regs 76 = q ∧ out.regs 77 = qe ∧ out.regs 84 = qp ∧
      out.arr = (((s.writeArr (s.regs 34) q).writeArr
        (s.regs 35) qe).writeArr (s.regs 36) qp).arr ∧
      out.regs 41 = s.regs 41 ∧ out.regs 42 = s.regs 42 ∧
      out.regs 43 = s.regs 43 ∧ out.regs 44 = s.regs 44 ∧
      out.regs 45 = s.regs 45 ∧ out.regs 46 = s.regs 46 ∧
      out.regs 31 = s.regs 31 ∧ out.regs 32 = s.regs 32 ∧
      out.regs 33 = s.regs 33 ∧ out.regs 34 = s.regs 34 ∧
      out.regs 35 = s.regs 35 ∧ out.regs 36 = s.regs 36 ∧
      out.regs 50 = s.regs 50 ∧ out.regs rPow = s.regs rPow ∧
      out.regs rBase = s.regs rBase := by
  let s1 := arun k s Cfg.markSecondFlagsBody
  let s2 := arun k s1 Cfg.markSecondCommitBody
  let s3 := arun k s2 Cfg.markSecondExponentBody
  have hflags := Cfg.markSecondFlagsBody_run k s hfirst
  dsimp only at hflags
  rcases hflags with
    ⟨_h67, _h68, _h69, h70, _h71, h72, h34, h44, hpow, hbase', harr0⟩
  have frame1 (r : Nat) (h : writes r Cfg.markSecondFlagsBody = false) :
      s1.regs r = s.regs r := arun_frame k r Cfg.markSecondFlagsBody h s
  have h41 : s1.regs 41 = s.regs 41 := frame1 41 (by decide)
  have h45 : s1.regs 45 = s.regs 45 := frame1 45 (by decide)
  have h46 : s1.regs 46 = s.regs 46 := frame1 46 (by decide)
  have h35 : s1.regs 35 = s.regs 35 := frame1 35 (by decide)
  have h36 : s1.regs 36 = s.regs 36 := frame1 36 (by decide)
  have hcommit := Cfg.markSecondCommitBody_run k s1 (by
      rw [h70]
      exact installQ_le_one _ _ _ _) (by
      rw [hbase']
      exact hbase) (by
      rw [h44]
      exact hq)
  dsimp only at hcommit
  rcases hcommit with
    ⟨_h73, _h74, _h75, h76, harr1, h34', h44', h70', hbase''⟩
  have frame2 (r : Nat) (h : writes r Cfg.markSecondCommitBody = false) :
      s2.regs r = s1.regs r := arun_frame k r Cfg.markSecondCommitBody h s1
  have h45' : s2.regs 45 = s1.regs 45 := frame2 45 (by decide)
  have h46' : s2.regs 46 = s1.regs 46 := frame2 46 (by decide)
  have h35' : s2.regs 35 = s1.regs 35 := frame2 35 (by decide)
  have h36' : s2.regs 36 = s1.regs 36 := frame2 36 (by decide)
  have h72' : s2.regs 72 = s1.regs 72 := frame2 72 (by decide)
  have hexp := Cfg.markSecondExponentBody_run k s2 (by
      rw [h45', h45, h72', h72]
      exact hqe)
  dsimp only at hexp
  rcases hexp with ⟨h77, harr2, h35'', h45'', h46'', h72''⟩
  have frame3 (r : Nat) (h : writes r Cfg.markSecondExponentBody = false) :
      s3.regs r = s2.regs r := arun_frame k r Cfg.markSecondExponentBody h s2
  have h36'' : s3.regs 36 = s2.regs 36 := frame3 36 (by decide)
  have hbase3 : s3.regs rBase = s2.regs rBase := frame3 rBase (by decide)
  have hprod := Cfg.markSecondProductBody_run k s3 (by
      rw [h72'', h72', h72]
      exact hitQ_le_one _ _ _ _ hbase0) (by
      rw [h46'', h46', h46]
      exact hqpp) (by
      rw [h46'', h46', h46, hbase3, hbase'', hbase']
      exact hqppMul)
  dsimp only at hprod
  rcases hprod with
    ⟨_h78, _h79, _h80, h84, harr3, h36''', h46''', h72''', hbase'''⟩
  have frame4 (r : Nat) (h : writes r Cfg.markSecondProductBody = false) :
      (arun k s3 Cfg.markSecondProductBody).regs r = s3.regs r :=
    arun_frame k r Cfg.markSecondProductBody h s3
  have harr1' := harr1
  have harr2' := harr2
  simp only [AState.writeArr] at harr0 harr1' harr2'
  rw [h34, h70, hbase', h44, harr0] at harr1'
  rw [h35', h35, h45', h45, h72', h72, harr1'] at harr2'
  simp only [Cfg.markSecondBody, Cfg.markSecondSelectBody, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (frame4 70 (by decide)).trans
      ((frame3 70 (by decide)).trans (h70'.trans h70))
  · exact h72'''.trans (h72''.trans (h72'.trans h72))
  · exact (frame4 76 (by decide)).trans
      ((frame3 76 (by decide)).trans (h76.trans (by
        rw [h70, hbase', h44]
        rfl)))
  · exact (frame4 77 (by decide)).trans
      (h77.trans (by rw [h45', h45, h72', h72]))
  · rw [h72'', h72', h72, h46'', h46', h46,
      hbase3, hbase'', hbase'] at h84
    exact h84
  · simp only [AState.writeArr] at harr3 ⊢
    rw [h36'', h36', h36, h72'', h72', h72, h46'', h46', h46,
      hbase3, hbase'', hbase', harr2'] at harr3
    exact harr3
  · exact (frame4 41 (by decide)).trans ((frame3 41 (by decide)).trans
      ((frame2 41 (by decide)).trans h41))
  · exact (frame4 42 (by decide)).trans ((frame3 42 (by decide)).trans
      ((frame2 42 (by decide)).trans (frame1 42 (by decide))))
  · exact (frame4 43 (by decide)).trans ((frame3 43 (by decide)).trans
      ((frame2 43 (by decide)).trans (frame1 43 (by decide))))
  · exact (frame4 44 (by decide)).trans ((frame3 44 (by decide)).trans
      (h44'.trans h44))
  · exact (frame4 45 (by decide)).trans (h45''.trans (h45'.trans h45))
  · exact h46'''.trans (h46''.trans (h46'.trans h46))
  · exact (frame4 31 (by decide)).trans ((frame3 31 (by decide)).trans
      ((frame2 31 (by decide)).trans (frame1 31 (by decide))))
  · exact (frame4 32 (by decide)).trans ((frame3 32 (by decide)).trans
      ((frame2 32 (by decide)).trans (frame1 32 (by decide))))
  · exact (frame4 33 (by decide)).trans ((frame3 33 (by decide)).trans
      ((frame2 33 (by decide)).trans (frame1 33 (by decide))))
  · exact (frame4 34 (by decide)).trans ((frame3 34 (by decide)).trans
      (h34'.trans h34))
  · exact (frame4 35 (by decide)).trans (h35''.trans (h35'.trans h35))
  · exact h36'''.trans (h36''.trans (h36'.trans h36))
  · exact (frame4 50 (by decide)).trans ((frame3 50 (by decide)).trans
      ((frame2 50 (by decide)).trans (frame1 50 (by decide))))
  · exact (frame4 rPow (by decide)).trans ((frame3 rPow (by decide)).trans
      ((frame2 rPow (by decide)).trans hpow))
  · exact hbase'''.trans (hbase3.trans (hbase''.trans hbase'))

/-! ## Composed seven-plane cell transition -/

/-- Raw physical contents of one seven-plane cell.  The three product fields
retain the program's zero sentinel for the empty product. -/
structure PlaneCell where
  prod : Nat
  p : Nat
  pe : Nat
  pProd : Nat
  q : Nat
  qe : Nat
  qProd : Nat
  deriving Repr, DecidableEq

@[ext] theorem PlaneCell.ext {x y : PlaneCell}
    (hprod : x.prod = y.prod) (hp : x.p = y.p) (hpe : x.pe = y.pe)
    (hpp : x.pProd = y.pProd) (hq : x.q = y.q) (hqe : x.qe = y.qe)
    (hqpp : x.qProd = y.qProd) : x = y := by
  cases x
  cases y
  simp_all

/-- The cell already loaded into registers `40` through `46`. -/
def loadedCell (s : AState) : PlaneCell :=
  ⟨s.regs 40, s.regs 41, s.regs 42, s.regs 43,
    s.regs 44, s.regs 45, s.regs 46⟩

/-- Logical effect of one live prime-power hit on all seven raw planes. -/
def PlaneCell.markPower (x : PlaneCell) (pow base : Nat) : PlaneCell :=
  let ph := hitP pow base x.p
  let qh := hitQ pow base x.p x.q
  { prod := nonzeroProduct x.prod * base
    p := nextP pow base x.p
    pe := x.pe + ph
    pProd := nextPowerProduct ph x.pProd base
    q := nextQ pow base x.p x.q
    qe := x.qe + qh
    qProd := nextPowerProduct qh x.qProd base }

/-- Write a logical cell at the seven addresses already selected in registers
`30` through `36`. -/
def writeLoadedCell (s : AState) (x : PlaneCell) : AState :=
  let s := s.writeArr (s.regs 30) x.prod
  let s := s.writeArr (s.regs 31) x.p
  let s := s.writeArr (s.regs 32) x.pe
  let s := s.writeArr (s.regs 33) x.pProd
  let s := s.writeArr (s.regs 34) x.q
  let s := s.writeArr (s.regs 35) x.qe
  s.writeArr (s.regs 36) x.qProd

/-- Read the seven live planes at one window offset. -/
def Cfg.readPlaneCell (c : Cfg) (j : Nat) (s : AState) : PlaneCell :=
  ⟨s.arr j, s.arr (j + c.segLen), s.arr (j + 2 * c.segLen),
    s.arr (j + 3 * c.segLen), s.arr (j + 4 * c.segLen),
    s.arr (j + 5 * c.segLen), s.arr (j + 6 * c.segLen)⟩

/-- Write all seven live planes at one window offset. -/
def Cfg.writePlaneCell (c : Cfg) (j : Nat) (s : AState)
    (x : PlaneCell) : AState :=
  let s := s.writeArr j x.prod
  let s := s.writeArr (j + c.segLen) x.p
  let s := s.writeArr (j + 2 * c.segLen) x.pe
  let s := s.writeArr (j + 3 * c.segLen) x.pProd
  let s := s.writeArr (j + 4 * c.segLen) x.q
  let s := s.writeArr (j + 5 * c.segLen) x.qe
  s.writeArr (j + 6 * c.segLen) x.qProd

theorem Cfg.readPlaneCell_congr (c : Cfg) (j : Nat) (s t : AState)
    (harr : s.arr = t.arr) : c.readPlaneCell j s = c.readPlaneCell j t := by
  apply PlaneCell.ext <;> simp only [Cfg.readPlaneCell]
  all_goals exact congrFun harr _

/-- Positive plane width makes all seven addresses distinct, so reading a
freshly written physical cell returns precisely the logical record. -/
theorem Cfg.readPlaneCell_writePlaneCell (c : Cfg) (j : Nat) (s : AState)
    (x : PlaneCell) (hL : 0 < c.segLen) :
    c.readPlaneCell j (c.writePlaneCell j s x) = x := by
  have hmul {a b : Nat} (hab : a ≠ b) :
      a * c.segLen ≠ b * c.segLen := by
    intro heq
    exact hab (Nat.mul_right_cancel hL heq)
  have hzero {a : Nat} (ha : a ≠ 0) : a * c.segLen ≠ 0 := by
    simpa using hmul ha
  have hone {b : Nat} (hb : 1 ≠ b) : c.segLen ≠ b * c.segLen := by
    simpa using hmul hb
  apply PlaneCell.ext <;>
    simp [Cfg.readPlaneCell, Cfg.writePlaneCell, AState.writeArr,
      hmul, hzero, hone]
  all_goals omega

/-- The selected-address writer is the physical plane writer when registers
`30` through `36` carry the live addresses. -/
theorem Cfg.writeLoadedCell_eq_writePlaneCell (c : Cfg) (j : Nat)
    (s : AState) (x : PlaneCell)
    (h30 : s.regs 30 = j)
    (h31 : s.regs 31 = j + c.segLen)
    (h32 : s.regs 32 = j + 2 * c.segLen)
    (h33 : s.regs 33 = j + 3 * c.segLen)
    (h34 : s.regs 34 = j + 4 * c.segLen)
    (h35 : s.regs 35 = j + 5 * c.segLen)
    (h36 : s.regs 36 = j + 6 * c.segLen) :
    writeLoadedCell s x = c.writePlaneCell j s x := by
  simp only [writeLoadedCell, Cfg.writePlaneCell, AState.writeArr_regs,
    h30, h31, h32, h33, h34, h35, h36]

/-- One live marking event implements exactly `PlaneCell.markPower`.  The
proof composes the all-product, first-prime, and second-prime refinements; it
never asks the simplifier to normalize the combined 43-instruction block. -/
theorem Cfg.markCellBody_run (k : Nat) (s : AState)
    (hbase0 : s.regs rBase ≠ 0) (hbase : s.regs rBase < M)
    (hprod : nonzeroProduct (s.regs 40) < M)
    (hprodMul : nonzeroProduct (s.regs 40) * s.regs rBase < M)
    (hp : s.regs 41 < M)
    (hpe : s.regs 42 + hitP (s.regs rPow) (s.regs rBase) (s.regs 41) < M)
    (hpp : nonzeroProduct (s.regs 43) < M)
    (hppMul : nonzeroProduct (s.regs 43) * s.regs rBase < M)
    (hq : s.regs 44 < M)
    (hqe : s.regs 45 + hitQ (s.regs rPow) (s.regs rBase)
      (s.regs 41) (s.regs 44) < M)
    (hqpp : nonzeroProduct (s.regs 46) < M)
    (hqppMul : nonzeroProduct (s.regs 46) * s.regs rBase < M) :
    let next := (loadedCell s).markPower (s.regs rPow) (s.regs rBase)
    let out := arun k s Cfg.markCellBody
    out.arr = (writeLoadedCell s next).arr ∧
      out.regs rPow = s.regs rPow ∧ out.regs rBase = s.regs rBase := by
  let s1 := arun k s Cfg.markAllProductBody
  let s2 := arun k s1 Cfg.markFirstBody
  have hall := Cfg.markAllProductBody_run k s hprod hprodMul
  dsimp only at hall
  rcases hall with ⟨_h47, _h48, _h49, harr0, h30, h40, hbase'⟩
  have frame1 (r : Nat) (h : writes r Cfg.markAllProductBody = false) :
      s1.regs r = s.regs r := arun_frame k r Cfg.markAllProductBody h s
  have hfirst := Cfg.markFirstBody_run k s1 (by
      rw [frame1 rBase (by decide)]
      exact hbase0) (by
      rw [hbase']
      exact hbase) (by
      rw [frame1 41 (by decide)]
      exact hp) (by
      rw [frame1 42 (by decide), frame1 rPow (by decide), hbase',
        frame1 41 (by decide)]
      exact hpe) (by
      rw [frame1 43 (by decide)]
      exact hpp) (by
      rw [frame1 43 (by decide), hbase']
      exact hppMul)
  dsimp only at hfirst
  rcases hfirst with
    ⟨h50, _h54, _h58, _h59, _h66, harr1, h41, h42, h43, h44, h45, h46,
      h31, h32, h33, h34, h35, h36, hpow, hbase''⟩
  have hsecond := Cfg.markSecondBody_run k s2 (by
      rw [h50, hpow, hbase'']) (by
      rw [hbase'']
      exact hbase0) (by
      rw [hbase'']
      exact hbase) (by
      rw [h44, frame1 44 (by decide)]
      exact hq) (by
      rw [h45, h44, h41, hpow, hbase'', frame1 45 (by decide),
        frame1 44 (by decide), frame1 41 (by decide)]
      exact hqe) (by
      rw [h46, frame1 46 (by decide)]
      exact hqpp) (by
      rw [h46, hbase'', frame1 46 (by decide)]
      exact hqppMul)
  dsimp only at hsecond
  rcases hsecond with
    ⟨_h70, _h72, _h76, _h77, _h84, harr2, _h41', _h42', _h43', _h44',
      _h45', _h46', _h31', _h32', _h33', _h34', _h35', _h36', _h50',
      hpow', hbase'''⟩
  have harr1' := harr1
  simp only [AState.writeArr] at harr0 harr1'
  rw [frame1 31 (by decide), frame1 32 (by decide),
    frame1 33 (by decide), frame1 rPow (by decide), hbase',
    frame1 41 (by decide), frame1 42 (by decide), frame1 43 (by decide),
    harr0] at harr1'
  simp only [Cfg.markCellBody, arun_append]
  refine ⟨?_, hpow'.trans (hpow.trans (frame1 rPow (by decide))),
    hbase'''.trans (hbase''.trans hbase')⟩
  simp only [AState.writeArr] at harr2 ⊢
  rw [h34, h35, h36, hpow, hbase'', h41, h44, h45, h46,
    frame1 34 (by decide), frame1 35 (by decide), frame1 36 (by decide),
    frame1 rPow (by decide), hbase', frame1 41 (by decide),
    frame1 44 (by decide), frame1 45 (by decide), frame1 46 (by decide),
    harr1'] at harr2
  simpa only [loadedCell, PlaneCell.markPower, writeLoadedCell,
    AState.writeArr_regs, AState.writeArr] using harr2

/-- Address specialization of `markCellBody_run`: after one live event, a
physical read of the seven planes is exactly the logical `markPower` result. -/
theorem Cfg.markCellBody_read_run (c : Cfg) (k j : Nat) (s : AState)
    (hL : 0 < c.segLen)
    (h30 : s.regs 30 = j)
    (h31 : s.regs 31 = j + c.segLen)
    (h32 : s.regs 32 = j + 2 * c.segLen)
    (h33 : s.regs 33 = j + 3 * c.segLen)
    (h34 : s.regs 34 = j + 4 * c.segLen)
    (h35 : s.regs 35 = j + 5 * c.segLen)
    (h36 : s.regs 36 = j + 6 * c.segLen)
    (hbase0 : s.regs rBase ≠ 0) (hbase : s.regs rBase < M)
    (hprod : nonzeroProduct (s.regs 40) < M)
    (hprodMul : nonzeroProduct (s.regs 40) * s.regs rBase < M)
    (hp : s.regs 41 < M)
    (hpe : s.regs 42 + hitP (s.regs rPow) (s.regs rBase) (s.regs 41) < M)
    (hpp : nonzeroProduct (s.regs 43) < M)
    (hppMul : nonzeroProduct (s.regs 43) * s.regs rBase < M)
    (hq : s.regs 44 < M)
    (hqe : s.regs 45 + hitQ (s.regs rPow) (s.regs rBase)
      (s.regs 41) (s.regs 44) < M)
    (hqpp : nonzeroProduct (s.regs 46) < M)
    (hqppMul : nonzeroProduct (s.regs 46) * s.regs rBase < M) :
    let next := (loadedCell s).markPower (s.regs rPow) (s.regs rBase)
    let out := arun k s Cfg.markCellBody
    c.readPlaneCell j out = next ∧ out.regs rPow = s.regs rPow ∧
      out.regs rBase = s.regs rBase := by
  have hrun := Cfg.markCellBody_run k s hbase0 hbase hprod hprodMul hp hpe
    hpp hppMul hq hqe hqpp hqppMul
  dsimp only at hrun
  rcases hrun with ⟨harr, hpow, hbase'⟩
  let next := (loadedCell s).markPower (s.regs rPow) (s.regs rBase)
  let out := arun k s Cfg.markCellBody
  have hselected : writeLoadedCell s next = c.writePlaneCell j s next :=
    c.writeLoadedCell_eq_writePlaneCell j s next h30 h31 h32 h33 h34 h35 h36
  have hread : c.readPlaneCell j out =
      c.readPlaneCell j (writeLoadedCell s next) :=
    c.readPlaneCell_congr j out (writeLoadedCell s next) harr
  refine ⟨hread.trans ?_, hpow, hbase'⟩
  rw [hselected]
  exact c.readPlaneCell_writePlaneCell j s next hL

/-- Machine bit which is one exactly when two words differ. -/
def neBit (x y : Nat) : Nat := if x ≠ y then 1 else 0

def Cfg.budgetFailure (c : Cfg) (round pi : Nat) : Nat :=
  eqBit round (c.markSteps - 1) * neBit pi c.tableLen

theorem Cfg.budgetFailure_le_one (c : Cfg) (round pi : Nat) :
    c.budgetFailure round pi ≤ 1 := by
  by_cases hr : round = c.markSteps - 1 <;>
    by_cases hp : pi = c.tableLen <;>
      simp [Cfg.budgetFailure, eqBit, neBit, hr, hp]

/-- A failure counter bounded by the current round can absorb the current
Boolean failure without wrapping.  This is the counter premise used by the
whole mark-loop induction. -/
theorem Cfg.budgetFailure_add_lt_word (c : Cfg) (round pi counter : Nat)
    (hcounter : counter ≤ round) (hround : round < c.markSteps)
    (hsteps : c.markSteps < M) :
    counter + c.budgetFailure round pi < M := by
  have hfailure := c.budgetFailure_le_one round pi
  omega

def advanceActive (inMark pastWindow : Nat) : Nat := inMark * pastWindow

def Cfg.powerFits (c : Cfg) (pow base : Nat) : Nat :=
  if pow * base ≤ c.hi then 1 else 0

def Cfg.bumpPower (c : Cfg) (inMark pastWindow pow base : Nat) : Nat :=
  advanceActive inMark pastWindow * c.powerFits pow base

def Cfg.stepPrime (c : Cfg) (inMark pastWindow pow base : Nat) : Nat :=
  advanceActive inMark pastWindow - c.bumpPower inMark pastWindow pow base

/-- The power decision is exact: an exhausted window position either advances
to the next power when it remains in range, or advances to the next prime. -/
theorem Cfg.markAdvancePowerBody_run (c : Cfg) (k : Nat) (s : AState)
    (h10 : s.regs 10 ≤ 1) (h25 : s.regs 25 ≤ 1)
    (hmul : s.regs rPow * s.regs rBase < M) (hhi : c.hi < M) :
    let active := advanceActive (s.regs 10) (s.regs 25)
    let bump := c.bumpPower (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let step := c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let out := arun k s c.markAdvancePowerBody
    out.regs 85 = active ∧
      out.regs 86 = s.regs rPow * s.regs rBase ∧
      out.regs 87 = c.powerFits (s.regs rPow) (s.regs rBase) ∧
      out.regs 88 = bump ∧ out.regs 89 = step ∧
      out.regs rPow = s.regs rPow ∧ out.regs rBase = s.regs rBase ∧
      out.arr = s.arr := by
  have hmul37 : s.regs 3 * s.regs 7 < 18446744073709551616 := by
    simpa [rPow, rBase, M] using hmul
  have hmulMod :
      (s.regs 3 * s.regs 7) % 18446744073709551616 =
        s.regs 3 * s.regs 7 := Nat.mod_eq_of_lt hmul37
  have hhiN : c.hi < 18446744073709551616 := by simpa [M] using hhi
  have hhiMod : c.hi % 18446744073709551616 = c.hi :=
    Nat.mod_eq_of_lt hhiN
  by_cases ha : s.regs 10 = 0
  · by_cases hb : s.regs 25 = 0
    · simp [Cfg.markAdvancePowerBody, arun, astep, AState.writeReg,
        sdest, sval, denoteOperand, denoteOp, advanceActive, Cfg.powerFits,
        Cfg.bumpPower, Cfg.stepPrime, ha, hb, hmulMod, hhiMod,
        rPow, rBase, M]
    · have hb1 : s.regs 25 = 1 := by omega
      simp [Cfg.markAdvancePowerBody, arun, astep, AState.writeReg,
        sdest, sval, denoteOperand, denoteOp, advanceActive, Cfg.powerFits,
        Cfg.bumpPower, Cfg.stepPrime, ha, hb1, hmulMod, hhiMod,
        rPow, rBase, M]
  · have ha1 : s.regs 10 = 1 := by omega
    by_cases hb : s.regs 25 = 0
    · simp [Cfg.markAdvancePowerBody, arun, astep, AState.writeReg,
        sdest, sval, denoteOperand, denoteOp, advanceActive, Cfg.powerFits,
        Cfg.bumpPower, Cfg.stepPrime, ha1, hb, hmulMod, hhiMod,
        rPow, rBase, M]
    · have hb1 : s.regs 25 = 1 := by omega
      by_cases hf : s.regs rPow * s.regs rBase ≤ c.hi
      · have hf37 : s.regs 3 * s.regs 7 ≤ c.hi := by
          simpa [rPow, rBase] using hf
        simp [Cfg.markAdvancePowerBody, arun, astep, AState.writeReg,
          sdest, sval, denoteOperand, denoteOp, advanceActive, Cfg.powerFits,
          Cfg.bumpPower, Cfg.stepPrime, ha1, hb1, hf37,
          hmulMod, hhiMod, rPow, rBase, M]
      · have hf37 : ¬s.regs 3 * s.regs 7 ≤ c.hi := by
          simpa [rPow, rBase] using hf
        simp [Cfg.markAdvancePowerBody, arun, astep, AState.writeReg,
          sdest, sval, denoteOperand, denoteOp, advanceActive, Cfg.powerFits,
          Cfg.bumpPower, Cfg.stepPrime, ha1, hb1, hf37,
          hmulMod, hhiMod, rPow, rBase, M]

def clampPi (K candidate : Nat) : Nat :=
  if candidate > K then K else candidate

theorem clampPi_le (K candidate : Nat) : clampPi K candidate ≤ K := by
  unfold clampPi
  split <;> omega

/-- The prime-table index advances by the selected bit and clamps exactly at
the sentinel row `tableLen`. -/
theorem Cfg.markAdvancePiBody_run (c : Cfg) (k : Nat) (s : AState)
    (hsum : s.regs rPi + s.regs 89 < M) (hK : c.tableLen < M) :
    let candidate := s.regs rPi + s.regs 89
    let out := arun k s c.markAdvancePiBody
    out.regs 90 = candidate ∧
      out.regs 91 = (if candidate > c.tableLen then 1 else 0) ∧
      out.regs 92 = (if candidate > c.tableLen then 0 else 1) ∧
      out.regs 93 = (if candidate > c.tableLen then 0 else candidate) ∧
      out.regs 94 = (if candidate > c.tableLen then c.tableLen else 0) ∧
      out.regs rPi = clampPi c.tableLen candidate ∧
      out.regs 89 = s.regs 89 ∧ out.arr = s.arr := by
  have hsum2 : s.regs 2 + s.regs 89 < 18446744073709551616 := by
    simpa [rPi, M] using hsum
  have hsumMod :
      (s.regs 2 + s.regs 89) % 18446744073709551616 =
        s.regs 2 + s.regs 89 := Nat.mod_eq_of_lt hsum2
  have hKN : c.tableLen < 18446744073709551616 := by simpa [M] using hK
  have hKMod : c.tableLen % 18446744073709551616 = c.tableLen :=
    Nat.mod_eq_of_lt hKN
  by_cases hover : s.regs rPi + s.regs 89 > c.tableLen
  · have hover2 : s.regs 2 + s.regs 89 > c.tableLen := by
      simpa [rPi] using hover
    simp [Cfg.markAdvancePiBody, arun, astep, AState.writeReg, sdest,
      sval, denoteOperand, denoteOp, clampPi, hover2,
      hsumMod, hKMod, rPi, M]
  · have hover2 : ¬s.regs 2 + s.regs 89 > c.tableLen := by
      simpa [rPi] using hover
    simp [Cfg.markAdvancePiBody, arun, astep, AState.writeReg, sdest,
      sval, denoteOperand, denoteOp, clampPi, hover2,
      hsumMod, hKMod, rPi, M]

/-- The selected prime-table index addresses and loads its exact sentinel or
prime row. -/
theorem Cfg.markAdvanceLoadBody_run (c : Cfg) (k : Nat) (s : AState)
    (haddr : s.regs rPi + c.tableBase < M) :
    let address := s.regs rPi + c.tableBase
    let out := arun k s c.markAdvanceLoadBody
    out.regs 95 = address ∧ out.regs 96 = s.arr address ∧
      out.regs rPi = s.regs rPi ∧ out.arr = s.arr := by
  have haddr2 : s.regs 2 + c.tableBase < 18446744073709551616 := by
    simpa [rPi, M] using haddr
  have hbase : c.tableBase < 18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) haddr2
  simp [Cfg.markAdvanceLoadBody, arun, astep, AState.writeReg, sdest,
    sval, denoteOperand, denoteOp, Nat.mod_eq_of_lt haddr2,
    Nat.mod_eq_of_lt hbase, rPi, M]

def nextPowValue (active bump step oldPow nextPow nextPrime : Nat) : Nat :=
  bump * nextPow + step * nextPrime + (1 - active) * oldPow

def nextBaseValue (step oldBase nextPrime : Nat) : Nat :=
  step * nextPrime + (1 - step) * oldBase

/-- The cursor value block selects exactly one of: retain the current power,
advance to its next power, or install the next prime-table row. -/
theorem Cfg.markAdvanceValueBody_run (k : Nat) (s : AState)
    (hactive : s.regs 85 ≤ 1) (hbump : s.regs 88 ≤ 1)
    (hstep : s.regs 89 ≤ 1)
    (hmodes : s.regs 88 + s.regs 89 = s.regs 85)
    (hjpow : s.regs rJ + s.regs rPow < M)
    (hpowOut : nextPowValue (s.regs 85) (s.regs 88) (s.regs 89)
      (s.regs rPow) (s.regs 86) (s.regs 96) < M)
    (hbaseOut : nextBaseValue (s.regs 89) (s.regs rBase) (s.regs 96) < M) :
    let powOut := nextPowValue (s.regs 85) (s.regs 88) (s.regs 89)
      (s.regs rPow) (s.regs 86) (s.regs 96)
    let baseOut := nextBaseValue (s.regs 89) (s.regs rBase) (s.regs 96)
    let out := arun k s Cfg.markAdvanceValueBody
    out.regs 97 = 1 - s.regs 85 ∧
      out.regs 98 = s.regs rJ + s.regs rPow ∧
      out.regs rPow = powOut ∧ out.regs rBase = baseOut ∧
      out.regs 85 = s.regs 85 ∧ out.regs 88 = s.regs 88 ∧
      out.regs 89 = s.regs 89 ∧ out.regs 96 = s.regs 96 ∧
      out.regs rJ = s.regs rJ ∧ out.arr = s.arr := by
  have hjpow43 : s.regs 4 + s.regs 3 < 18446744073709551616 := by
    simpa [rJ, rPow, M] using hjpow
  have hjpowMod :
      (s.regs 4 + s.regs 3) % 18446744073709551616 =
        s.regs 4 + s.regs 3 := Nat.mod_eq_of_lt hjpow43
  by_cases ha : s.regs 85 = 0
  · have hb : s.regs 88 = 0 := by omega
    have hs : s.regs 89 = 0 := by omega
    have hp3 : s.regs 3 < 18446744073709551616 := by
      simpa [nextPowValue, ha, hb, hs, rPow, M] using hpowOut
    have hb7 : s.regs 7 < 18446744073709551616 := by
      simpa [nextBaseValue, hs, rBase, M] using hbaseOut
    simp [Cfg.markAdvanceValueBody, arun, astep, AState.writeReg, sdest,
      sval, denoteOperand, denoteOp, nextPowValue, nextBaseValue,
      ha, hb, hs, hjpowMod, Nat.mod_eq_of_lt hp3,
      Nat.mod_eq_of_lt hb7, rJ, rPow, rBase, M]
  · have ha1 : s.regs 85 = 1 := by omega
    by_cases hb : s.regs 88 = 0
    · have hs : s.regs 89 = 1 := by omega
      have hn96 : s.regs 96 < 18446744073709551616 := by
        simpa [nextPowValue, ha1, hb, hs, rPow, M] using hpowOut
      simp [Cfg.markAdvanceValueBody, arun, astep, AState.writeReg, sdest,
        sval, denoteOperand, denoteOp, nextPowValue, nextBaseValue,
        ha1, hb, hs, hjpowMod, Nat.mod_eq_of_lt hn96,
        rJ, rPow, rBase, M]
    · have hb1 : s.regs 88 = 1 := by omega
      have hs : s.regs 89 = 0 := by omega
      have hn86 : s.regs 86 < 18446744073709551616 := by
        simpa [nextPowValue, ha1, hb1, hs, rPow, M] using hpowOut
      have hb7 : s.regs 7 < 18446744073709551616 := by
        simpa [nextBaseValue, hs, rBase, M] using hbaseOut
      simp [Cfg.markAdvanceValueBody, arun, astep, AState.writeReg, sdest,
        sval, denoteOperand, denoteOp, nextPowValue, nextBaseValue,
        ha1, hb1, hs, hjpowMod, Nat.mod_eq_of_lt hn86,
        Nat.mod_eq_of_lt hb7, rJ, rPow, rBase, M]

def startOffset (windowBase pow : Nat) : Nat :=
  (pow - windowBase % pow) % pow

def Cfg.selectedOffset (c : Cfg) (pi windowBase pow : Nat) : Nat :=
  if pi = c.tableLen then c.segLen + 1 else startOffset windowBase pow

def nextOffset (active selected fallback : Nat) : Nat :=
  active * selected + (1 - active) * fallback

/-- The offset block computes the first multiple of the selected power in the
window, uses `segLen+1` at the sentinel row, and otherwise retains the current
multiple offset. -/
theorem Cfg.markAdvanceOffsetBody_run (c : Cfg) (k : Nat) (s : AState)
    (hactive : s.regs 85 ≤ 1) (hnot : s.regs 97 = 1 - s.regs 85)
    (hpow0 : s.regs rPow ≠ 0) (hpow : s.regs rPow < M)
    (hK : c.tableLen < M) (hL1 : c.segLen + 1 < M)
    (hfallback : s.regs 98 < M) :
    let selected := c.selectedOffset (s.regs rPi) (s.regs rW)
      (s.regs rPow)
    let value := nextOffset (s.regs 85) selected (s.regs 98)
    let out := arun k s c.markAdvanceOffsetBody
    out.regs 116 = s.regs rW % s.regs rPow ∧
      out.regs 118 = startOffset (s.regs rW) (s.regs rPow) ∧
      out.regs 119 = eqBit (s.regs rPi) c.tableLen ∧
      out.regs 123 = selected ∧ out.regs rJ = value ∧
      out.regs rPi = s.regs rPi ∧ out.regs rPow = s.regs rPow ∧
      out.regs rW = s.regs rW ∧ out.arr = s.arr := by
  have hpow3 : s.regs 3 ≠ 0 := by simpa [rPow] using hpow0
  have hpow3M : s.regs 3 < 18446744073709551616 := by
    simpa [rPow, M] using hpow
  have hrem : s.regs 6 % s.regs 3 < s.regs 3 :=
    Nat.mod_lt _ (Nat.pos_of_ne_zero hpow3)
  have hremM : s.regs 6 % s.regs 3 < 18446744073709551616 :=
    Nat.lt_trans hrem hpow3M
  have hpow3Word : s.regs 3 < M := by simpa [rPow] using hpow
  have hremWord : s.regs 6 % s.regs 3 < M :=
    Nat.lt_trans hrem hpow3Word
  have hremMod :
      (s.regs 6 % s.regs 3) % 18446744073709551616 =
        s.regs 6 % s.regs 3 := Nat.mod_eq_of_lt hremM
  have hsubM : s.regs 3 - s.regs 6 % s.regs 3 <
      18446744073709551616 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow3M
  have hsubWordBound : s.regs 3 - s.regs 6 % s.regs 3 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow3Word
  have hsubWord :
      (s.regs 3 + (M - s.regs 6 % s.regs 3)) % M =
        s.regs 3 - s.regs 6 % s.regs 3 := by
    have hle : s.regs 6 % s.regs 3 ≤ s.regs 3 := Nat.le_of_lt hrem
    have hrew : s.regs 3 + (M - s.regs 6 % s.regs 3) =
        M + (s.regs 3 - s.regs 6 % s.regs 3) := by omega
    rw [hrew, Nat.add_mod_left, Nat.mod_eq_of_lt hsubWordBound]
  have hsubWordN :
      (s.regs 3 + (18446744073709551616 - s.regs 6 % s.regs 3)) %
          18446744073709551616 =
        s.regs 3 - s.regs 6 % s.regs 3 := by simpa [M] using hsubWord
  have hoffRaw : (s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3 <
      18446744073709551616 :=
    Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hpow3)) hpow3M
  have hoffRawMod :
      ((s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3) %
          18446744073709551616 =
        (s.regs 3 - s.regs 6 % s.regs 3) % s.regs 3 :=
    Nat.mod_eq_of_lt hoffRaw
  have hKN : c.tableLen < 18446744073709551616 := by simpa [M] using hK
  have hKMod : c.tableLen % 18446744073709551616 = c.tableLen :=
    Nat.mod_eq_of_lt hKN
  have hL1N : c.segLen + 1 < 18446744073709551616 := by
    simpa [M] using hL1
  have hfN : s.regs 98 < 18446744073709551616 := by
    simpa [M] using hfallback
  by_cases ha : s.regs 85 = 0
  · have h97 : s.regs 97 = 1 := by omega
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      simp [Cfg.markAdvanceOffsetBody, arun, astep, AState.writeReg, sdest,
        sval, denoteOperand, denoteOp, Cfg.selectedOffset, startOffset,
        nextOffset, eqBit, ha, h97, hp2, hpow3, hremMod,
        hsubWordN, hoffRawMod, hKMod, hL1N, Nat.mod_eq_of_lt hfN,
        rPi, rPow, rW, rJ, M]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      simp [Cfg.markAdvanceOffsetBody, arun, astep, AState.writeReg, sdest,
        sval, denoteOperand, denoteOp, Cfg.selectedOffset, startOffset,
        nextOffset, eqBit, ha, h97, hp2, hpow3, hremMod,
        hsubWordN, hoffRawMod, hKMod, Nat.mod_eq_of_lt hfN,
        rPi, rPow, rW, rJ, M]
  · have ha1 : s.regs 85 = 1 := by omega
    have h97 : s.regs 97 = 0 := by omega
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      simp [Cfg.markAdvanceOffsetBody, arun, astep, AState.writeReg, sdest,
        sval, denoteOperand, denoteOp, Cfg.selectedOffset, startOffset,
        nextOffset, eqBit, ha1, h97, hp2, hpow3, hremMod,
        hsubWordN, hoffRawMod, hKMod, hL1N,
        rPi, rPow, rW, rJ, M]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      simp [Cfg.markAdvanceOffsetBody, arun, astep, AState.writeReg, sdest,
        sval, denoteOperand, denoteOp, Cfg.selectedOffset, startOffset,
        nextOffset, eqBit, ha1, h97, hp2, hpow3, hremMod,
        hsubWordN, hoffRawMod, hKMod,
        rPi, rPow, rW, rJ, M]

/-- The budget guard records failure exactly when the final configured mark
round has not exhausted the prime table. -/
theorem Cfg.markBudgetBody_run (c : Cfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hviol : s.regs rViol + c.budgetFailure (s.regs rR) (s.regs rPi) < M)
    (hvmark : s.regs rVMark + c.budgetFailure (s.regs rR) (s.regs rPi) < M) :
    let failure := c.budgetFailure (s.regs rR) (s.regs rPi)
    let out := arun k s c.markBudgetBody
    out.regs 126 = eqBit (s.regs rR) (c.markSteps - 1) ∧
      out.regs 127 = neBit (s.regs rPi) c.tableLen ∧
      out.regs 128 = failure ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧
      out.regs rR = s.regs rR ∧ out.regs rPi = s.regs rPi ∧
      out.arr = s.arr := by
  have hTm1 : c.markSteps - 1 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hT
  have hTm1N : c.markSteps - 1 < 18446744073709551616 := by
    simpa [M] using hTm1
  have hTm1ModN :
      (c.markSteps - 1) % 18446744073709551616 = c.markSteps - 1 :=
    Nat.mod_eq_of_lt hTm1N
  have hKN : c.tableLen < 18446744073709551616 := by simpa [M] using hK
  have hKModN : c.tableLen % 18446744073709551616 = c.tableLen :=
    Nat.mod_eq_of_lt hKN
  have toNum {x : Nat} (hx : x < M) : x < 18446744073709551616 := by
    simpa [M] using hx
  by_cases hr : s.regs rR = c.markSteps - 1
  · have hr5 : s.regs 5 = c.markSteps - 1 := by simpa [rR] using hr
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      have hv8 : s.regs 8 < M := by
        simpa [Cfg.budgetFailure, eqBit, neBit, hr, hp, rViol] using hviol
      have hm177 : s.regs 177 < M := by
        simpa [Cfg.budgetFailure, eqBit, neBit, hr, hp, rVMark] using hvmark
      simp [Cfg.markBudgetBody, arun, astep, AState.writeReg, sdest, sval,
        denoteOperand, denoteOp, Cfg.budgetFailure, eqBit, neBit,
        hr5, hp2, hTm1ModN, hKModN,
        Nat.mod_eq_of_lt (toNum hv8), Nat.mod_eq_of_lt (toNum hm177),
        rR, rPi, rViol, rVMark, M]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      have hv8 : s.regs 8 + 1 < M := by
        simpa [Cfg.budgetFailure, eqBit, neBit, hr, hp, rViol] using hviol
      have hm177 : s.regs 177 + 1 < M := by
        simpa [Cfg.budgetFailure, eqBit, neBit, hr, hp, rVMark] using hvmark
      simp [Cfg.markBudgetBody, arun, astep, AState.writeReg, sdest, sval,
        denoteOperand, denoteOp, Cfg.budgetFailure, eqBit, neBit,
        hr5, hp2, hTm1ModN, hKModN,
        Nat.mod_eq_of_lt (toNum hv8), Nat.mod_eq_of_lt (toNum hm177),
        rR, rPi, rViol, rVMark, M]
  · have hr5 : s.regs 5 ≠ c.markSteps - 1 := by simpa [rR] using hr
    by_cases hp : s.regs rPi = c.tableLen
    · have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      have hv8 : s.regs 8 < M := by
        simpa [Cfg.budgetFailure, eqBit, neBit, hr, hp, rViol] using hviol
      have hm177 : s.regs 177 < M := by
        simpa [Cfg.budgetFailure, eqBit, neBit, hr, hp, rVMark] using hvmark
      simp [Cfg.markBudgetBody, arun, astep, AState.writeReg, sdest, sval,
        denoteOperand, denoteOp, Cfg.budgetFailure, eqBit, neBit,
        hr5, hp2, hTm1ModN, hKModN,
        Nat.mod_eq_of_lt (toNum hv8), Nat.mod_eq_of_lt (toNum hm177),
        rR, rPi, rViol, rVMark, M]
    · have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      have hv8 : s.regs 8 < M := by
        simpa [Cfg.budgetFailure, eqBit, neBit, hr, hp, rViol] using hviol
      have hm177 : s.regs 177 < M := by
        simpa [Cfg.budgetFailure, eqBit, neBit, hr, hp, rVMark] using hvmark
      simp [Cfg.markBudgetBody, arun, astep, AState.writeReg, sdest, sval,
        denoteOperand, denoteOp, Cfg.budgetFailure, eqBit, neBit,
        hr5, hp2, hTm1ModN, hKModN,
        Nat.mod_eq_of_lt (toNum hv8), Nat.mod_eq_of_lt (toNum hm177),
        rR, rPi, rViol, rVMark, M]

/-! ## Composed cursor-selection stage -/

/-- The emitted power-choice and prime-index blocks compose to the exact pure
mode bits and clamped table cursor.  Keeping this composition separate from
the subsequent load/value/offset stages prevents the simplifier from seeing
the complete cursor pipeline at once. -/
theorem Cfg.markAdvanceSelectBody_run (c : Cfg) (k : Nat) (s : AState)
    (h10 : s.regs 10 ≤ 1) (h25 : s.regs 25 ≤ 1)
    (hmul : s.regs rPow * s.regs rBase < M) (hhi : c.hi < M)
    (hsum : s.regs rPi +
      c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase) < M)
    (hK : c.tableLen < M) :
    let active := advanceActive (s.regs 10) (s.regs 25)
    let bump := c.bumpPower (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let step := c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let candidate := s.regs rPi + step
    let out := arun k s c.markAdvanceSelectBody
    out.regs 85 = active ∧ out.regs 86 = s.regs rPow * s.regs rBase ∧
      out.regs 88 = bump ∧ out.regs 89 = step ∧
      out.regs rPi = clampPi c.tableLen candidate ∧
      out.regs rPow = s.regs rPow ∧ out.regs rBase = s.regs rBase ∧
      out.regs rJ = s.regs rJ ∧ out.regs rW = s.regs rW ∧
      out.arr = s.arr := by
  let selected := arun k s c.markAdvancePowerBody
  have hpower := c.markAdvancePowerBody_run k s h10 h25 hmul hhi
  dsimp only at hpower
  rcases hpower with
    ⟨h85, h86, _h87, h88, h89, hpow, hbase, harr1⟩
  have frame1 (r : Nat)
      (h : writes r c.markAdvancePowerBody = false) :
      selected.regs r = s.regs r :=
    arun_frame k r c.markAdvancePowerBody h s
  have hpi1 : selected.regs rPi = s.regs rPi :=
    frame1 rPi (by rfl)
  have hj1 : selected.regs rJ = s.regs rJ :=
    frame1 rJ (by rfl)
  have hw1 : selected.regs rW = s.regs rW :=
    frame1 rW (by rfl)
  have hpiRun := c.markAdvancePiBody_run k selected (by
      rw [hpi1, h89]
      exact hsum) hK
  dsimp only at hpiRun
  rcases hpiRun with
    ⟨_h90, _h91, _h92, _h93, _h94, hpi, h89', harr2⟩
  let out := arun k selected c.markAdvancePiBody
  have frame2 (r : Nat) (h : writes r c.markAdvancePiBody = false) :
      out.regs r = selected.regs r :=
    arun_frame k r c.markAdvancePiBody h selected
  simp only [Cfg.markAdvanceSelectBody, arun_append]
  refine ⟨frame2 85 (by rfl) |>.trans h85,
    frame2 86 (by rfl) |>.trans h86,
    frame2 88 (by rfl) |>.trans h88,
    h89'.trans h89,
    ?_,
    (frame2 rPow (by rfl)).trans hpow,
    (frame2 rBase (by rfl)).trans hbase,
    (frame2 rJ (by rfl)).trans hj1,
    (frame2 rW (by rfl)).trans hw1,
    harr2.trans harr1⟩
  have hpi' := hpi
  rw [hpi1, h89] at hpi'
  exact hpi'

/-- The next emitted stage loads exactly the table word selected by the
composed and clamped cursor. -/
theorem Cfg.markAdvanceSelectLoadBody_run (c : Cfg) (k : Nat) (s : AState)
    (h10 : s.regs 10 ≤ 1) (h25 : s.regs 25 ≤ 1)
    (hmul : s.regs rPow * s.regs rBase < M) (hhi : c.hi < M)
    (hsum : s.regs rPi +
      c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase) < M)
    (hK : c.tableLen < M)
    (haddr : clampPi c.tableLen
      (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)) + c.tableBase < M) :
    let active := advanceActive (s.regs 10) (s.regs 25)
    let bump := c.bumpPower (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let step := c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let address := piOut + c.tableBase
    let out := arun k s (c.markAdvanceSelectBody ++ c.markAdvanceLoadBody)
    out.regs 85 = active ∧ out.regs 86 = s.regs rPow * s.regs rBase ∧
      out.regs 88 = bump ∧ out.regs 89 = step ∧
      out.regs rPi = piOut ∧ out.regs 96 = s.arr address ∧
      out.regs rPow = s.regs rPow ∧ out.regs rBase = s.regs rBase ∧
      out.regs rJ = s.regs rJ ∧ out.regs rW = s.regs rW ∧
      out.arr = s.arr := by
  let selected := arun k s c.markAdvanceSelectBody
  have hselect := c.markAdvanceSelectBody_run k s h10 h25 hmul hhi hsum hK
  dsimp only at hselect
  rcases hselect with
    ⟨h85, h86, h88, h89, hpi, hpow, hbase, hj, hw, harr1⟩
  have hload := c.markAdvanceLoadBody_run k selected (by
      rw [hpi]
      exact haddr)
  dsimp only at hload
  rcases hload with ⟨_h95, h96, hpi', harr2⟩
  let out := arun k selected c.markAdvanceLoadBody
  have frame (r : Nat) (h : writes r c.markAdvanceLoadBody = false) :
      out.regs r = selected.regs r :=
    arun_frame k r c.markAdvanceLoadBody h selected
  simp only [arun_append]
  refine ⟨(frame 85 (by rfl)).trans h85,
    (frame 86 (by rfl)).trans h86,
    (frame 88 (by rfl)).trans h88,
    (frame 89 (by rfl)).trans h89,
    hpi'.trans hpi,
    ?_,
    (frame rPow (by rfl)).trans hpow,
    (frame rBase (by rfl)).trans hbase,
    (frame rJ (by rfl)).trans hj,
    (frame rW (by rfl)).trans hw,
    harr2.trans harr1⟩
  have h96' := h96
  rw [hpi, harr1] at h96'
  exact h96'

/-- The value stage selects the retained power, next power, or next prime
from the exact clamped table load. -/
theorem Cfg.markAdvanceSelectLoadValueBody_run (c : Cfg) (k : Nat)
    (s : AState)
    (h10 : s.regs 10 ≤ 1) (h25 : s.regs 25 ≤ 1)
    (hmul : s.regs rPow * s.regs rBase < M) (hhi : c.hi < M)
    (hsum : s.regs rPi +
      c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase) < M)
    (hK : c.tableLen < M)
    (haddr : clampPi c.tableLen
      (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)) + c.tableBase < M)
    (hactive : advanceActive (s.regs 10) (s.regs 25) ≤ 1)
    (hbump : c.bumpPower (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase) ≤ 1)
    (hstep : c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase) ≤ 1)
    (hmodes : c.bumpPower (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase) +
      c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase) =
      advanceActive (s.regs 10) (s.regs 25))
    (hjpow : s.regs rJ + s.regs rPow < M)
    (hpowOut :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      let nextPrime := s.arr (piOut + c.tableBase)
      nextPowValue (advanceActive (s.regs 10) (s.regs 25))
        (c.bumpPower (s.regs 10) (s.regs 25)
          (s.regs rPow) (s.regs rBase)) step
        (s.regs rPow) (s.regs rPow * s.regs rBase) nextPrime < M)
    (hbaseOut :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      let nextPrime := s.arr (piOut + c.tableBase)
      nextBaseValue step (s.regs rBase) nextPrime < M) :
    let active := advanceActive (s.regs 10) (s.regs 25)
    let bump := c.bumpPower (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let step := c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let nextPrime := s.arr (piOut + c.tableBase)
    let powOut := nextPowValue active bump step
      (s.regs rPow) (s.regs rPow * s.regs rBase) nextPrime
    let baseOut := nextBaseValue step (s.regs rBase) nextPrime
    let out := arun k s
      ((c.markAdvanceSelectBody ++ c.markAdvanceLoadBody) ++
        Cfg.markAdvanceValueBody)
    out.regs 85 = active ∧ out.regs 88 = bump ∧ out.regs 89 = step ∧
      out.regs 97 = 1 - active ∧
      out.regs 98 = s.regs rJ + s.regs rPow ∧
      out.regs rPi = piOut ∧ out.regs rPow = powOut ∧
      out.regs rBase = baseOut ∧ out.regs rJ = s.regs rJ ∧
      out.regs rW = s.regs rW ∧ out.arr = s.arr := by
  let loaded := arun k s
    (c.markAdvanceSelectBody ++ c.markAdvanceLoadBody)
  have hload := c.markAdvanceSelectLoadBody_run k s h10 h25 hmul hhi
    hsum hK haddr
  dsimp only at hload
  rcases hload with
    ⟨h85, h86, h88, h89, hpi, h96, hpow, hbase, hj, hw, harr1⟩
  have hvalue := Cfg.markAdvanceValueBody_run k loaded (by
      rw [h85]
      exact hactive) (by
      rw [h88]
      exact hbump) (by
      rw [h89]
      exact hstep) (by
      rw [h88, h89, h85]
      exact hmodes) (by
      rw [hj, hpow]
      exact hjpow) (by
      rw [h85, h88, h89, hpow, h86, h96]
      exact hpowOut) (by
      rw [h89, hbase, h96]
      exact hbaseOut)
  dsimp only at hvalue
  rcases hvalue with
    ⟨h97, h98, hpow', hbase', h85', h88', h89', _h96', hj', harr2⟩
  let out := arun k loaded Cfg.markAdvanceValueBody
  have frame (r : Nat) (h : writes r Cfg.markAdvanceValueBody = false) :
      out.regs r = loaded.regs r :=
    arun_frame k r Cfg.markAdvanceValueBody h loaded
  simp only [arun_append]
  rw [h85] at h97
  rw [hj, hpow] at h98
  rw [h85, h88, h89, hpow, h86, h96] at hpow'
  rw [h89, hbase, h96] at hbase'
  exact ⟨h85'.trans h85, h88'.trans h88, h89'.trans h89,
    h97, h98, (frame rPi (by rfl)).trans hpi, hpow', hbase',
    hj'.trans hj, (frame rW (by rfl)).trans hw, harr2.trans harr1⟩

/-- Word-safety and Boolean-mode obligations for the composed cursor value
prefix.  The production loop invariant will discharge this record once per
mark iteration. -/
structure CursorValuePre (c : Cfg) (s : AState) : Prop where
  h10 : s.regs 10 ≤ 1
  h25 : s.regs 25 ≤ 1
  hmul : s.regs rPow * s.regs rBase < M
  hhi : c.hi < M
  hsum : s.regs rPi +
    c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase) < M
  hK : c.tableLen < M
  haddr : clampPi c.tableLen
    (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)) + c.tableBase < M
  hactive : advanceActive (s.regs 10) (s.regs 25) ≤ 1
  hbump : c.bumpPower (s.regs 10) (s.regs 25)
    (s.regs rPow) (s.regs rBase) ≤ 1
  hstep : c.stepPrime (s.regs 10) (s.regs 25)
    (s.regs rPow) (s.regs rBase) ≤ 1
  hmodes : c.bumpPower (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase) +
    c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase) =
    advanceActive (s.regs 10) (s.regs 25)
  hjpow : s.regs rJ + s.regs rPow < M
  hpowOut :
    let step := c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let nextPrime := s.arr (piOut + c.tableBase)
    nextPowValue (advanceActive (s.regs 10) (s.regs 25))
      (c.bumpPower (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)) step
      (s.regs rPow) (s.regs rPow * s.regs rBase) nextPrime < M
  hbaseOut :
    let step := c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let nextPrime := s.arr (piOut + c.tableBase)
    nextBaseValue step (s.regs rBase) nextPrime < M

/-- Complete emitted cursor transition through power/prime choice, clamped
table load, value selection, and next-offset selection. -/
theorem Cfg.markAdvanceCursorPrefix_run (c : Cfg) (k : Nat) (s : AState)
    (hpre : CursorValuePre c s)
    (hpow0 :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      let nextPrime := s.arr (piOut + c.tableBase)
      nextPowValue (advanceActive (s.regs 10) (s.regs 25))
        (c.bumpPower (s.regs 10) (s.regs 25)
          (s.regs rPow) (s.regs rBase)) step
        (s.regs rPow) (s.regs rPow * s.regs rBase) nextPrime ≠ 0)
    (hL1 : c.segLen + 1 < M) :
    let active := advanceActive (s.regs 10) (s.regs 25)
    let bump := c.bumpPower (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let step := c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let nextPrime := s.arr (piOut + c.tableBase)
    let powOut := nextPowValue active bump step
      (s.regs rPow) (s.regs rPow * s.regs rBase) nextPrime
    let baseOut := nextBaseValue step (s.regs rBase) nextPrime
    let fallback := s.regs rJ + s.regs rPow
    let jOut := nextOffset active (c.selectedOffset piOut (s.regs rW) powOut)
      fallback
    let out := arun k s
      (((c.markAdvanceSelectBody ++ c.markAdvanceLoadBody) ++
        Cfg.markAdvanceValueBody) ++ c.markAdvanceOffsetBody)
    out.regs 85 = active ∧ out.regs 88 = bump ∧ out.regs 89 = step ∧
      out.regs rPi = piOut ∧ out.regs rPow = powOut ∧
      out.regs rBase = baseOut ∧ out.regs rJ = jOut ∧
      out.regs rW = s.regs rW ∧ out.arr = s.arr := by
  let valued := arun k s
    ((c.markAdvanceSelectBody ++ c.markAdvanceLoadBody) ++
      Cfg.markAdvanceValueBody)
  have hvalue := c.markAdvanceSelectLoadValueBody_run k s
    hpre.h10 hpre.h25 hpre.hmul hpre.hhi hpre.hsum hpre.hK hpre.haddr
    hpre.hactive hpre.hbump hpre.hstep hpre.hmodes hpre.hjpow
    hpre.hpowOut hpre.hbaseOut
  dsimp only at hvalue
  rcases hvalue with
    ⟨h85, h88, h89, h97, h98, hpi, hpow, hbase, _hj, hw, harr1⟩
  have hoffset := c.markAdvanceOffsetBody_run k valued (by
      rw [h85]
      exact hpre.hactive) (by
      rw [h97, h85]) (by
      rw [hpow]
      exact hpow0) (by
      rw [hpow]
      exact hpre.hpowOut) hpre.hK hL1 (by
      rw [h98]
      exact hpre.hjpow)
  dsimp only at hoffset
  rcases hoffset with
    ⟨_h116, _h118, _h119, _h123, hjOut, hpi', hpow', hw', harr2⟩
  let out := arun k valued c.markAdvanceOffsetBody
  have frame (r : Nat) (h : writes r c.markAdvanceOffsetBody = false) :
      out.regs r = valued.regs r :=
    arun_frame k r c.markAdvanceOffsetBody h valued
  simp only [arun_append]
  rw [h85, hpi, hw, hpow, h98] at hjOut
  exact ⟨(frame 85 (by rfl)).trans h85,
    (frame 88 (by rfl)).trans h88,
    (frame 89 (by rfl)).trans h89,
    hpi'.trans hpi, hpow'.trans hpow,
    (frame rBase (by rfl)).trans hbase,
    hjOut, hw'.trans hw, harr2.trans harr1⟩

/-- The complete emitted advance block implements the pure cursor transition
and records exactly the configured final-round budget failure.  This theorem
keeps the already-composed cursor proof opaque while checking the five budget
instructions, so elaboration never expands the full block at once. -/
theorem Cfg.markAdvanceBody_run (c : Cfg) (k : Nat) (s : AState)
    (hpre : CursorValuePre c s)
    (hpow0 :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      let nextPrime := s.arr (piOut + c.tableBase)
      nextPowValue (advanceActive (s.regs 10) (s.regs 25))
        (c.bumpPower (s.regs 10) (s.regs 25)
          (s.regs rPow) (s.regs rBase)) step
        (s.regs rPow) (s.regs rPow * s.regs rBase) nextPrime ≠ 0)
    (hL1 : c.segLen + 1 < M) (hT : c.markSteps < M)
    (hviol :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      s.regs rViol + c.budgetFailure (s.regs rR) piOut < M)
    (hvmark :
      let step := c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)
      let piOut := clampPi c.tableLen (s.regs rPi + step)
      s.regs rVMark + c.budgetFailure (s.regs rR) piOut < M) :
    let active := advanceActive (s.regs 10) (s.regs 25)
    let bump := c.bumpPower (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let step := c.stepPrime (s.regs 10) (s.regs 25)
      (s.regs rPow) (s.regs rBase)
    let piOut := clampPi c.tableLen (s.regs rPi + step)
    let nextPrime := s.arr (piOut + c.tableBase)
    let powOut := nextPowValue active bump step
      (s.regs rPow) (s.regs rPow * s.regs rBase) nextPrime
    let baseOut := nextBaseValue step (s.regs rBase) nextPrime
    let fallback := s.regs rJ + s.regs rPow
    let jOut := nextOffset active (c.selectedOffset piOut (s.regs rW) powOut)
      fallback
    let failure := c.budgetFailure (s.regs rR) piOut
    let out := arun k s c.markAdvanceBody
    out.regs rPi = piOut ∧ out.regs rPow = powOut ∧
      out.regs rBase = baseOut ∧ out.regs rJ = jOut ∧
      out.regs rViol = s.regs rViol + failure ∧
      out.regs rVMark = s.regs rVMark + failure ∧
      out.regs rR = s.regs rR ∧ out.regs rW = s.regs rW ∧
      out.arr = s.arr := by
  let cursorPrefix :=
    (((c.markAdvanceSelectBody ++ c.markAdvanceLoadBody) ++
      Cfg.markAdvanceValueBody) ++ c.markAdvanceOffsetBody)
  let advanced := arun k s cursorPrefix
  have hcursor := c.markAdvanceCursorPrefix_run k s hpre hpow0 hL1
  dsimp only at hcursor
  rcases hcursor with
    ⟨_h85, _h88, _h89, hpi, hpow, hbase, hj, hw, harr1⟩
  have framePrefix (r : Nat) (h : writes r cursorPrefix = false) :
      advanced.regs r = s.regs r :=
    arun_frame k r cursorPrefix h s
  have hr := framePrefix rR (by rfl)
  have hviolFrame := framePrefix rViol (by rfl)
  have hvmarkFrame := framePrefix rVMark (by rfl)
  have hbudget := c.markBudgetBody_run k advanced hT hpre.hK (by
      rw [hviolFrame, hr, hpi]
      exact hviol) (by
      rw [hvmarkFrame, hr, hpi]
      exact hvmark)
  dsimp only at hbudget
  rcases hbudget with
    ⟨_h126, _h127, _h128, hviolOut, hvmarkOut, hrOut, hpiOut, harr2⟩
  let out := arun k advanced c.markBudgetBody
  have frameBudget (r : Nat) (h : writes r c.markBudgetBody = false) :
      out.regs r = advanced.regs r :=
    arun_frame k r c.markBudgetBody h advanced
  have result :
      out.regs rPi = clampPi c.tableLen
          (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
            (s.regs rPow) (s.regs rBase)) ∧
        out.regs rPow = nextPowValue
          (advanceActive (s.regs 10) (s.regs 25))
          (c.bumpPower (s.regs 10) (s.regs 25)
            (s.regs rPow) (s.regs rBase))
          (c.stepPrime (s.regs 10) (s.regs 25)
            (s.regs rPow) (s.regs rBase))
          (s.regs rPow) (s.regs rPow * s.regs rBase)
          (s.arr (clampPi c.tableLen
            (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
              (s.regs rPow) (s.regs rBase)) + c.tableBase)) ∧
        out.regs rBase = nextBaseValue
          (c.stepPrime (s.regs 10) (s.regs 25)
            (s.regs rPow) (s.regs rBase)) (s.regs rBase)
          (s.arr (clampPi c.tableLen
            (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
              (s.regs rPow) (s.regs rBase)) + c.tableBase)) ∧
        out.regs rJ = nextOffset
          (advanceActive (s.regs 10) (s.regs 25))
          (c.selectedOffset
            (clampPi c.tableLen
              (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
                (s.regs rPow) (s.regs rBase)))
            (s.regs rW)
            (nextPowValue (advanceActive (s.regs 10) (s.regs 25))
              (c.bumpPower (s.regs 10) (s.regs 25)
                (s.regs rPow) (s.regs rBase))
              (c.stepPrime (s.regs 10) (s.regs 25)
                (s.regs rPow) (s.regs rBase))
              (s.regs rPow) (s.regs rPow * s.regs rBase)
              (s.arr (clampPi c.tableLen
                (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
                  (s.regs rPow) (s.regs rBase)) + c.tableBase))))
          (s.regs rJ + s.regs rPow) ∧
        out.regs rViol = s.regs rViol +
          c.budgetFailure (s.regs rR)
            (clampPi c.tableLen
              (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
                (s.regs rPow) (s.regs rBase))) ∧
        out.regs rVMark = s.regs rVMark +
          c.budgetFailure (s.regs rR)
            (clampPi c.tableLen
              (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
                (s.regs rPow) (s.regs rBase))) ∧
        out.regs rR = s.regs rR ∧ out.regs rW = s.regs rW ∧
        out.arr = s.arr := by
    refine ⟨hpiOut.trans hpi,
      (frameBudget rPow (by rfl)).trans hpow,
      (frameBudget rBase (by rfl)).trans hbase,
      (frameBudget rJ (by rfl)).trans hj, ?_, ?_,
      hrOut.trans hr, (frameBudget rW (by rfl)).trans hw,
      harr2.trans harr1⟩
    · calc
        out.regs rViol = advanced.regs rViol +
            c.budgetFailure (advanced.regs rR) (advanced.regs rPi) := hviolOut
        _ = s.regs rViol +
            c.budgetFailure (s.regs rR)
              (clampPi c.tableLen
                (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
                  (s.regs rPow) (s.regs rBase))) := by
          rw [hviolFrame, hr, hpi]
    · calc
        out.regs rVMark = advanced.regs rVMark +
            c.budgetFailure (advanced.regs rR) (advanced.regs rPi) := hvmarkOut
        _ = s.regs rVMark +
            c.budgetFailure (s.regs rR)
              (clampPi c.tableLen
                (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
                  (s.regs rPow) (s.regs rBase))) := by
          rw [hvmarkFrame, hr, hpi]
  simpa only [Cfg.markAdvanceBody, Cfg.markAdvanceCursorBody,
    List.append_assoc, arun_append, out, advanced, cursorPrefix] using result

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

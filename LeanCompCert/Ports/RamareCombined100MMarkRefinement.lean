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

/-- Install the second prime exactly on the first power of a new base once a
first prime exists and the second-prime plane is still empty. -/
def installQ (pow base p q : Nat) : Nat :=
  eqBit pow base * nonzeroBit p * zeroBit q

def hitQ (pow base p q : Nat) : Nat :=
  installQ pow base p q + eqBit base q

def nextQ (pow base p q : Nat) : Nat :=
  installQ pow base p q * base + (1 - installQ pow base p q) * q

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

/-- Machine bit which is one exactly when two words differ. -/
def neBit (x y : Nat) : Nat := if x ≠ y then 1 else 0

def Cfg.budgetFailure (c : Cfg) (round pi : Nat) : Nat :=
  eqBit round (c.markSteps - 1) * neBit pi c.tableLen

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

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

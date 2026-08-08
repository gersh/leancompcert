import LeanCompCert.Ports.ArraySegMobiusScheduleFold

/-!
# Finite cell decoding for the segmented Möbius sieve

The compiled marking theorem ends at `rootCellFold`.  This module gives that
finite computation a canonical integer-valued output and proves the machine
decoder presents the corresponding one-hot `muSig`.  The function is named
`rootFoldValue`, not “the Möbius function”: identifying it with a paper or
library Möbius definition is a separate number-theoretic theorem.
-/

namespace LeanCompCert.Ports.ArraySegMobiusCellRep

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.MobiusResidueRealisation

private theorem bit_cases {x : Nat} (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  omega

private theorem bit_xor_le (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) :
    x ^^^ y ≤ 1 := by
  rcases bit_cases hx with rfl | rfl <;>
    rcases bit_cases hy with rfl | rfl <;> decide

private theorem bit_mod (x : Nat) (hx : x ≤ 1) : x % M = x :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hx (by decide))

private theorem one_sub_bit_mod (x : Nat) (hx : x ≤ 1) :
    (1 + (M - x)) % M = 1 - x := by
  rcases bit_cases hx with rfl | rfl
  · rw [show 1 + (M - 0) = 1 + M by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by decide)
  · rw [show 1 + (M - 1) = M by
      rw [Nat.add_comm, Nat.sub_add_cancel (by decide : 1 ≤ M)],
      Nat.mod_self]

private theorem mul_bit_mod (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) :
    (x * y) % M = x * y := by
  exact Nat.mod_eq_of_lt (by
    have h := Nat.mul_le_mul hx hy
    have : 1 < M := by decide
    omega)

/-- The transparent decoder always emits two exclusive bits. -/
theorem decodeCell_bits (n prod flag : Nat) :
    let g := decodeCell n prod flag
    g.pos ≤ 1 ∧ g.neg ≤ 1 ∧ ¬(g.pos = 1 ∧ g.neg = 1) := by
  let prod1 := (prod + if prod = 0 then 1 else 0) % M
  let sq := (flag >>> 1) % M &&& 1
  let low := (flag &&& 1) % M
  let extra := if prod1 = n then 0 else 1
  let parity := low ^^^ extra
  have hsq : sq ≤ 1 := Nat.and_le_right
  have hlow : low ≤ 1 := by
    dsimp only [low]
    have h := Nat.and_le_right (n := flag) (m := 1)
    have hmod : (flag &&& 1) % M = flag &&& 1 := bit_mod _ h
    rw [hmod]
    exact h
  have hextra : extra ≤ 1 := by
    dsimp only [extra]
    split <;> omega
  have hpar : parity ≤ 1 := bit_xor_le low extra hlow hextra
  have hsqMod : sq % M = sq := bit_mod sq hsq
  have hparMod : parity % M = parity := bit_mod parity hpar
  have hsf : 1 - sq ≤ 1 := by omega
  have hinv : 1 - parity ≤ 1 := by omega
  change
    (((1 + (M - (((flag >>> 1) % M &&& 1) % M))) % M) *
          ((1 + (M - (((flag &&& 1) % M ^^^
            (if prod1 = n then 0 else 1)) % M))) % M)) % M ≤ 1 ∧
      (((1 + (M - (((flag >>> 1) % M &&& 1) % M))) % M) *
          (((flag &&& 1) % M ^^^
            (if prod1 = n then 0 else 1)) % M)) % M ≤ 1 ∧
      ¬(_ = 1 ∧ _ = 1)
  change
    (((1 + (M - (sq % M))) % M) *
          ((1 + (M - (parity % M))) % M)) % M ≤ 1 ∧
      (((1 + (M - (sq % M))) % M) * (parity % M)) % M ≤ 1 ∧
      ¬((((1 + (M - (sq % M))) % M) *
            ((1 + (M - (parity % M))) % M)) % M = 1 ∧
        (((1 + (M - (sq % M))) % M) * (parity % M)) % M = 1)
  rw [hsqMod, hparMod, one_sub_bit_mod sq hsq,
    one_sub_bit_mod parity hpar,
    mul_bit_mod (1 - sq) (1 - parity) hsf hinv,
    mul_bit_mod (1 - sq) parity hsf hpar]
  refine ⟨Nat.le_trans (Nat.mul_le_mul hsf hinv) (by omega),
    Nat.le_trans (Nat.mul_le_mul hsf hpar) (by omega), ?_⟩
  intro hboth
  change (1 - sq) * (1 - parity) = 1 ∧
    (1 - sq) * parity = 1 at hboth
  rcases bit_cases hpar with hpar0 | hpar1
  · have hz : (1 - sq) * parity = 0 := by rw [hpar0]; simp
    omega
  · have hz : (1 - sq) * (1 - parity) = 0 := by rw [hpar1]; simp
    omega

/-- Integer value encoded by one transparent decoded cell. -/
def decodedValue (n prod flag : Nat) : Int :=
  let g := decodeCell n prod flag
  if g.pos = 1 then 1 else if g.neg = 1 then -1 else 0

/-- Every runnable cell decoder has one of the three Möbius-shaped integer
values, independently of any number-theoretic interpretation. -/
theorem decodedValue_eq_or (n prod flag : Nat) :
    decodedValue n prod flag = 1 ∨ decodedValue n prod flag = -1 ∨
      decodedValue n prod flag = 0 := by
  by_cases hp : (decodeCell n prod flag).pos = 1
  · left
    simp [decodedValue, hp]
  · by_cases hn : (decodeCell n prod flag).neg = 1
    · right; left
      simp [decodedValue, hp, hn]
    · right; right
      simp [decodedValue, hp, hn]

private theorem sig_eq_muSig_of_bits (g : Sig) (n : Nat)
    (hn : g.n = n) (hgate : g.gate = 1)
    (hpos : g.pos ≤ 1) (hneg : g.neg ≤ 1)
    (hexcl : ¬(g.pos = 1 ∧ g.neg = 1)) :
    g = muSig
      (fun _ => if g.pos = 1 then 1 else if g.neg = 1 then -1 else 0) n := by
  cases g with
  | mk gn pos neg gate =>
      change gn = n at hn
      change gate = 1 at hgate
      change pos ≤ 1 at hpos
      change neg ≤ 1 at hneg
      change ¬(pos = 1 ∧ neg = 1) at hexcl
      subst gn
      subst gate
      change ({ n := n, pos := pos, neg := neg, gate := 1 } : Sig) = _
      rcases bit_cases hpos with rfl | rfl <;>
        rcases bit_cases hneg with rfl | rfl
      · simp [muSig]
      · simp [muSig]
      · simp [muSig]
      · exact False.elim (hexcl ⟨rfl, rfl⟩)

/-- The decoder is definitionally reconstructed by `muSig` from its finite
integer value; no number-theoretic premise is used here. -/
theorem decodeCell_eq_muSig_decodedValue (n prod flag : Nat) :
    decodeCell n prod flag =
      muSig (fun _ => decodedValue n prod flag) n := by
  let g := decodeCell n prod flag
  have hbits := decodeCell_bits n prod flag
  have h := sig_eq_muSig_of_bits g n (by rfl) (by rfl)
    hbits.1 hbits.2.1 hbits.2.2
  simpa [decodedValue, g] using h

/-- Runnable integer value of the finite represented-prime fold. -/
def rootFoldValue (ps : List Nat) (n : Nat) : Int :=
  let q := rootCellFold ps n
  decodedValue n q.prod q.flag

/-- The finite represented-prime fold always lands in `{-1, 0, 1}`. -/
theorem rootFoldValue_eq_or (ps : List Nat) (n : Nat) :
    rootFoldValue ps n = 1 ∨ rootFoldValue ps n = -1 ∨
      rootFoldValue ps n = 0 := by
  exact decodedValue_eq_or n _ _

/-- Transparent finite number-theoretic value of a represented-prime fold.
It is zero when a listed prime square divides `n`; otherwise its sign is the
parity of the listed prime divisors plus the decoder's possible one remaining
prime factor. -/
def finiteRootValue (ps : List Nat) (n : Nat) : Int :=
  let logic := rootLogicFold ps n
  let extra := if divisorProduct ps n = n then 0 else 1
  if logic.square then 0
  else if (divisorCount ps n + extra) % 2 = 0 then 1 else -1

/-- The machine-oriented decoder and the transparent finite
parity/square/product description agree. -/
theorem rootFoldValue_eq_finiteRootValue (ps : List Nat) (n : Nat)
    (hprime : ∀ p, p ∈ ps → LeanCompCert.Verified.PackedSieve.IsPrime p)
    (hordered : ps.Pairwise (· < ·))
    (hnPos : 0 < n) (hnM : n < M) :
    rootFoldValue ps n = finiteRootValue ps n := by
  have hdPos := divisorProduct_pos ps n hprime
  have hdM := divisorProduct_lt_modulus ps n hprime hordered hnPos hnM
  have hprod := rootCellFold_prod_eq_encoded ps n hprime hordered hnPos hnM
  have hprodDecode := encodedProduct_decode (divisorProduct ps n) hdPos hdM
  have hflag := rootCellFold_flag_eq_encode ps n
  have hpar := rootLogicFold_parity_eq ps n
  dsimp only [rootFoldValue, finiteRootValue, decodedValue]
  rw [hprod, hflag]
  unfold decodeCell
  rw [hprodDecode]
  simp only [encodeRootLogic, hpar]
  rcases Nat.eq_zero_or_pos (divisorCount ps n % 2) with hz | hpos
  · by_cases hs : (rootLogicFold ps n).square = true <;>
      by_cases hd : divisorProduct ps n = n <;>
      simp [hs, hz, hd, Nat.add_mod] <;> decide
  · have hr := Nat.mod_lt (divisorCount ps n) (by decide : 0 < 2)
    have ho : divisorCount ps n % 2 = 1 := by omega
    by_cases hs : (rootLogicFold ps n).square = true <;>
      by_cases hd : divisorProduct ps n = n <;>
      simp [hs, ho, hd, Nat.add_mod] <;> decide

/-- Every finite root fold satisfies `CellRepresents` for its explicitly
named executable value. -/
theorem rootCellFold_cellRepresents (ps : List Nat) (n : Nat) :
    let q := rootCellFold ps n
    CellRepresents (rootFoldValue ps) n q.prod q.flag := by
  dsimp only [CellRepresents, rootFoldValue]
  exact decodeCell_eq_muSig_decodedValue n
    (rootCellFold ps n).prod (rootCellFold ps n).flag

/-- Extensional form used after an instruction-level selected-cell theorem. -/
theorem cellRepresents_of_cell_eq_rootCellFold (ps : List Nat) (n : Nat)
    (cell : RootCellState) (hcell : cell = rootCellFold ps n) :
    CellRepresents (rootFoldValue ps) n cell.prod cell.flag := by
  subst cell
  exact rootCellFold_cellRepresents ps n

end LeanCompCert.Ports.ArraySegMobiusCellRep

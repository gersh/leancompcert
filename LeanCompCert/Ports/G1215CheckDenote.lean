import LeanCompCert.Ports.G1215CheckRun
import LeanCompCert.Ports.RS62LadderEncoding
import LeanCompCert.Ports.BlockedFold
import LeanCompCert.Ports.TrialDivisionFold

/-!
# From the staged blocks to the program's denotation

Layer two-and-a-half of the `G1215Check` port.  `Ports/G1215CheckRun.lean`
proved what each block does to an abstract register file; this module names
every `let` of `gRound` as a function of the incoming state, chases the
staged values through the eight stages under the invariant, and assembles

* `gRun_spec` — one flat round's effect on the carried registers is exactly
  `gRound`, and `Inv` is preserved;
* `gBody_defined` — the emitted body is defined at every visited index and
  agrees with `gRun` below the temporary cursor;
* `gProgram_denote` — **the whole program denotes the epilogue-corrected good
  flag of the flat `gRound` fold**, with no fold evaluated, so the theorem
  costs the same at `len = 8` and at `len = 10⁷`.

The one structural difference from the sibling `Ports/GFoldCheckRun.lean` is
the epilogue: `GFoldCheck`'s is empty, while this port re-tests the two exact
final sums there.  It is threaded through `denote_eq_foldl_mem`'s `fin`
argument as `gEpi`.

Nothing here evaluates a fold, and nothing here is a certificate.
-/

namespace LeanCompCert.Ports.G1215Check

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight

set_option maxRecDepth 4000

/-! ## §8 The per-round quantities, named -/

section Named

variable (c : Params) (k : Nat) (s : RegState)

/-- The round inside the candidate's block. -/
def qOf : Nat := k % c.R

/-- The candidate. -/
def nOf : Nat := c.lo + k / c.R

/-- The trial divisor. -/
def dOf : Nat := qOf c k + 2

/-- The cofactor after the per-candidate reset. -/
def m0Of : Nat := if qOf c k = 0 then nOf c k else s 1

/-- The totient product after the reset. -/
def phi0Of : Nat := if qOf c k = 0 then 1 else s 2

/-- The squarefree flag after the reset. -/
def sq0Of : Nat := if qOf c k = 0 then 1 else s 3

/-- The pass flag after the reset. -/
def pass0Of : Nat := if qOf c k = 0 then 0 else s 6

/-- The cofactor after the peel. -/
def m1Of : Nat :=
  if m0Of c k s % dOf c k = 0 then m0Of c k s / dOf c k else m0Of c k s

/-- The totient product after the peel. -/
def phi1Of : Nat :=
  if m0Of c k s % dOf c k = 0 then phi0Of c k s * (dOf c k - 1) else phi0Of c k s

/-- The squarefree flag after the peel. -/
def sq1Of : Nat :=
  if m0Of c k s % dOf c k = 0 ∧ m0Of c k s / dOf c k % dOf c k = 0 then 0
  else sq0Of c k s

/-- The decoded totient. -/
def phiFOf : Nat :=
  if 1 < m1Of c k s then phi1Of c k s * (m1Of c k s - 1) else phi1Of c k s

/-- The floor quotient `⌊2⁴⁴/φ⌋`. -/
def tqOf : Nat := 2 ^ 44 / phiFOf c k s

/-- The masked ceiling term. -/
def tUOf : Nat :=
  sq1Of c k s * (tqOf c k s + (if 2 ^ 44 % phiFOf c k s = 0 then 0 else 1))

/-- The masked floor term. -/
def tLOf : Nat := sq1Of c k s * tqOf c k s

/-- The upper accumulator after the masked step. -/
def accU1Of : Nat := (s 4 + (if qOf c k = c.tdiv then tUOf c k s else 0)) % M

/-- The lower accumulator after the masked step. -/
def accL1Of : Nat := (s 5 + (if qOf c k = c.tdiv then tLOf c k s else 0)) % M

/-- `⌊log₂ n⌋`. -/
def aUN : Nat := aOf (nOf c k)

/-- `⌊log₂ (n+1)⌋`. -/
def aLN : Nat := aOf (nOf c k + 1)

/-- Track `U`'s raw advance. -/
def x2UOf : Nat := advX (nOf c k) (aUN c k) (s 7)

/-- Track `U`'s renormalisation bit. -/
def gUOf : Nat := if 2 ^ 40 ≤ x2UOf c k s then 1 else 0

/-- Track `U`'s renormalised advance. -/
def xUAOf : Nat := x2UOf c k s / 2 ^ gUOf c k s - MB

/-- Track `U`'s round-`tdiv` initial mantissa. -/
def xUIOf : Nat := (nOf c k - 2 ^ aUN c k) * 2 ^ (39 - aUN c k)

/-- Track `U`'s mantissa after the select. -/
def xU1Of : Nat :=
  if qOf c k < c.tdiv then s 7
  else if qOf c k = c.tdiv then xUIOf c k else xUAOf c k s

/-- Track `U`'s unclamped exponent. -/
def kUNOf : Nat := s 8 + aUN c k + gUOf c k s

/-- Track `U`'s exponent after the select. -/
def kU1Of : Nat :=
  if qOf c k < c.tdiv then s 8
  else if qOf c k = c.tdiv then aUN c k
  else if kUNOf c k s ≤ KCAP then kUNOf c k s else KCAP

/-- Track `L`'s raw advance. -/
def x2LOf : Nat := advX (nOf c k + 1) (aLN c k) (s 9)

/-- Track `L`'s renormalisation bit. -/
def gLOf : Nat := if 2 ^ 40 ≤ x2LOf c k s then 1 else 0

/-- Track `L`'s renormalised advance. -/
def xLAOf : Nat := x2LOf c k s / 2 ^ gLOf c k s - MB

/-- Track `L`'s round-`tdiv` initial mantissa. -/
def xLIOf : Nat := (nOf c k + 1 - 2 ^ aLN c k) * 2 ^ (39 - aLN c k)

/-- Track `L`'s mantissa after the select. -/
def xL1Of : Nat :=
  if qOf c k < c.tdiv then s 9
  else if qOf c k = c.tdiv then xLIOf c k else xLAOf c k s

/-- Track `L`'s unclamped exponent. -/
def kLNOf : Nat := s 10 + aLN c k + gLOf c k s

/-- Track `L`'s exponent after the select. -/
def kL1Of : Nat :=
  if qOf c k < c.tdiv then s 10
  else if qOf c k = c.tdiv then aLN c k
  else if kLNOf c k s ≤ KCAP then kLNOf c k s else KCAP

/-- The pass flag after the round. -/
def pass1Of : Nat :=
  if qOf c k < c.tdiv then pass0Of c k s
  else pass0Of c k s ||| hitOf c (nOf c k) (qOf c k - c.tdiv + 1)
    (accU1Of c k s) (accL1Of c k s) (xU1Of c k s) (kU1Of c k s)
    (xL1Of c k s) (kL1Of c k s)

/-- The good flag after the round. -/
def goodOf : Nat :=
  if qOf c k = c.R - 1 then s 0 * pass1Of c k s else s 0

end Named

/-- `gRound`, in the named quantities. -/
theorem gRound_eq (c : Params) (k : Nat) (s : RegState) :
    gRound c k (valsOf s) =
      ⟨goodOf c k s, m1Of c k s, phi1Of c k s, sq1Of c k s, accU1Of c k s,
        accL1Of c k s, pass1Of c k s, xU1Of c k s, kU1Of c k s, xL1Of c k s,
        kL1Of c k s⟩ := rfl

/-! ## §7 bis The remaining stage specifications

`Ports/G1215CheckRun.lean` stops after stage `C12`.  The Padé operand blocks,
the two candidate blocks and the verdict blocks are specified here, in the
same style: a frame clause naming the written registers, then one value per
written register, with every `% M` truncation discharged from hypotheses the
caller supplies.  The `⚠` of §7 applies verbatim — where a block carries a
`2 ^ n` literal the value goal is opened by a `rfl`-stated `have` in the exact
shape `evalExpr`/`denoteOp` produce, because `simp` reduces `2 ^ 32` to its
numeral before `lit232` can fire. -/

/-- A `39`-bit mantissa's top `16` bits. -/
private theorem u16_lt {x : Nat} (hx : x < MB) : x / 2 ^ 23 < 2 ^ 16 := by
  have hMB : MB = 2 ^ 39 := rfl
  refine (Nat.div_lt_iff_lt_mul (by decide)).mpr ?_
  have h : (2:Nat) ^ 16 * 2 ^ 23 = 2 ^ 39 := by decide
  omega

/-- The mantissa advance's width budget, at a candidate that may sit exactly
on `2²⁴`.  `Ports/G1215CheckRun.lean`'s `advX_prod_lt` asks for `n < 2²⁴`,
which the successor track `n + 1` only satisfies with `≤`. -/
private theorem advX_prod_le {n x : Nat} (hx : x < MB) (hn : n ≤ 2 ^ 24) :
    (MB + x) * n < M := by
  have h1 : MB + x ≤ 2 ^ 40 - 1 := by simp only [MB] at hx ⊢; omega
  have h2 : (MB + x) * n ≤ (2 ^ 40 - 1) * 2 ^ 24 := Nat.mul_le_mul h1 hn
  have h3 : ((2:Nat) ^ 40 - 1) * 2 ^ 24 < M := by decide
  omega

/-- **Stage C8a**, at the weaker candidate bound the successor track needs. -/
theorem blkC8a_spec' (k : Nat) (t : RegState) (xL n aL : Nat)
    (h9 : t 9 = xL) (h13 : t 13 = n) (h29 : t 29 = aL)
    (hx : xL < MB) (hn : n + 1 ≤ 2 ^ 24) :
    (∀ i, i ≠ 36 → run k t blkC8a i = t i) ∧
    run k t blkC8a 36 = advX (n + 1) aL xL := by
  have hn1M : n + 1 < M := by
    have h2 : (2:Nat) ^ 24 < M := two24_lt_M
    omega
  refine ⟨?_, ?_⟩
  · intro i e36
    simp [run, blkC8a, RegState.set, e36]
  · have hval : run k t blkC8a 36 =
        ((((2 ^ 39 % M + t 9) % M * ((t 13 + 1 % M) % M)) % M) >>> t 29) % M :=
      rfl
    have e1 : (2 ^ 39 + xL) % M = 2 ^ 39 + xL := modId (mbAdd_lt hx)
    have e2 : ((2 ^ 39 + xL) * (n + 1)) % M = (2 ^ 39 + xL) * (n + 1) :=
      modId (advX_prod_le hx hn)
    rw [hval, h9, h13, h29, lit239, lit1, modId hn1M, e1, e2,
      Nat.shiftRight_eq_div_pow]
    exact modId (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (advX_prod_le hx hn))

/-- **Stage C13a**: track `U`'s truncated mantissa's fractional part. -/
theorem blkC13a_spec (k : Nat) (t : RegState) (xU : Nat)
    (h7 : t 7 = xU) (hx : xU < MB) :
    (∀ i, i ≠ 41 → run k t blkC13a i = t i) ∧
    run k t blkC13a 41 = xU / 2 ^ 23 := by
  refine ⟨?_, ?_⟩
  · intro i e41
    simp [run, blkC13a, RegState.set, e41]
  · have hval : run k t blkC13a 41 = (t 7 >>> (23 % M)) % M := rfl
    have hlt : xU / 2 ^ 23 < M := by
      have h1 := u16_lt hx
      have h2 : (2:Nat) ^ 16 < M := by decide
      omega
    rw [hval, h7, lit23, Nat.shiftRight_eq_div_pow]
    exact modId hlt

/-- **Stage C13b**: track `U`'s `17`-bit mantissa. -/
theorem blkC13b_spec (k : Nat) (t : RegState) (u : Nat)
    (h41 : t 41 = u) (hu : u < 2 ^ 16) :
    (∀ i, i ≠ 42 → run k t blkC13b i = t i) ∧
    run k t blkC13b 42 = 2 ^ 16 + u := by
  refine ⟨?_, ?_⟩
  · intro i e42
    simp [run, blkC13b, RegState.set, e42]
  · have hval : run k t blkC13b 42 = (2 ^ 16 % M + t 41) % M := rfl
    have hlt : 2 ^ 16 + u < M := by
      have h : (2:Nat) ^ 17 < M := by decide
      omega
    rw [hval, h41, lit216]
    exact modId hlt

/-- The Padé-lower numerator's truncations, hoisted: `omega`'s cost is the
size of the local context, and inside the stage proof it is forty deep. -/
private theorem loNum_facts {u : Nat} (hu : u < 2 ^ 16) :
    u * u % M = u * u ∧ u * 2 ^ 17 % M = u * 2 ^ 17 ∧
      (u * u + u * 2 ^ 17) % M = u * u + u * 2 ^ 17 ∧
      3 * (u * u + u * 2 ^ 17) % M = 3 * (u * u + u * 2 ^ 17) ∧
      3 * (u * u + u * 2 ^ 17) * 2 ^ 28 % M
        = 3 * (u * u + u * 2 ^ 17) * 2 ^ 28 ∧
      3 * (u * u + u * 2 ^ 17) * 2 ^ 28 < M ∧
      3 * (u * u + u * 2 ^ 17) * 2 ^ 28 ≤ 3 * 2 ^ 34 * 2 ^ 28 := by
  have h1 : u * u < 2 ^ 32 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hu hu) (by decide)
  have h2 : u * 2 ^ 17 < 2 ^ 33 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_le hu (Nat.le_refl _) (by decide)) (by decide)
  have h3 : u * u + u * 2 ^ 17 < 2 ^ 34 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add h1 h2) (by decide)
  have h4 : 3 * (u * u + u * 2 ^ 17) ≤ 3 * 2 ^ 34 :=
    Nat.mul_le_mul_left _ (Nat.le_of_lt h3)
  have h5 : 3 * (u * u + u * 2 ^ 17) * 2 ^ 28 ≤ 3 * 2 ^ 34 * 2 ^ 28 :=
    Nat.mul_le_mul_right _ h4
  have h6 : 3 * (u * u + u * 2 ^ 17) * 2 ^ 28 < M :=
    Nat.lt_of_le_of_lt h5 (by decide)
  exact ⟨modId (Nat.lt_trans h1 (by decide)),
    modId (Nat.lt_trans h2 (by decide)),
    modId (Nat.lt_trans h3 (by decide)),
    modId (Nat.lt_of_le_of_lt h4 (by decide)), modId h6, h6, h5⟩

/-- The Padé-lower denominator's band and truncations. -/
private theorem loDen_facts {y : Nat} (hyge : 2 ^ 16 ≤ y)
    (hylt : y < 2 ^ 17) :
    y * y % M = y * y ∧ y * 2 ^ 18 % M = y * 2 ^ 18 ∧
      (y * y + y * 2 ^ 18) % M = y * y + y * 2 ^ 18 ∧
      (2 ^ 32 + (y * y + y * 2 ^ 18)) % M = 2 ^ 32 + (y * y + y * 2 ^ 18) ∧
      2 ^ 33 ≤ 2 ^ 32 + (y * y + y * 2 ^ 18) ∧
      2 ^ 32 + (y * y + y * 2 ^ 18) < 2 ^ 37 := by
  have h1 : y * y < 2 ^ 34 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hylt hylt) (by decide)
  have h2 : y * 2 ^ 18 < 2 ^ 35 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_le hylt (Nat.le_refl _) (by decide)) (by decide)
  have h3 : y * y + y * 2 ^ 18 < 2 ^ 36 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add h1 h2) (by decide)
  have h4 : 2 ^ 32 + (y * y + y * 2 ^ 18) < 2 ^ 37 :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left h3 (2 ^ 32)) (by decide)
  have hlow : (2:Nat) ^ 32 ≤ y * y :=
    Nat.le_trans (by decide) (Nat.mul_le_mul hyge hyge)
  have h5 : (2:Nat) ^ 33 ≤ 2 ^ 32 + (y * y + y * 2 ^ 18) := by
    have h6 : (2:Nat) ^ 33 = 2 ^ 32 + 2 ^ 32 := by decide
    omega
  exact ⟨modId (Nat.lt_trans h1 (by decide)),
    modId (Nat.lt_trans h2 (by decide)),
    modId (Nat.lt_trans h3 (by decide)),
    modId (Nat.lt_trans h4 (by decide)), h5, h4⟩

/-- **Stage C13c**: track `U`'s Padé-lower operands. -/
theorem blkC13c_spec (k : Nat) (t : RegState) (u y : Nat)
    (h41 : t 41 = u) (h42 : t 42 = y) (hy : y = 2 ^ 16 + u) (hu : u < 2 ^ 16) :
    (∀ i, i ≠ 43 → i ≠ 44 → run k t blkC13c i = t i) ∧
    run k t blkC13c 43 = 3 * (u * u + u * 2 ^ 17) * 2 ^ 28 ∧
    run k t blkC13c 44 = 2 ^ 32 + (y * y + y * 2 ^ 18) := by
  have hyge : 2 ^ 16 ≤ y := by omega
  have hylt : y < 2 ^ 17 := by
    have h : (2:Nat) ^ 16 + 2 ^ 16 = 2 ^ 17 := by decide
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro i e43 e44
    simp [run, blkC13c, RegState.set, e43, e44]
  · obtain ⟨e1, e2, e3, e4, e5, -⟩ := loNum_facts hu
    have hval : run k t blkC13c 43 =
        ((((3 % M) * ((((t 41 * t 41) % M) + ((t 41 <<< (17 % M)) % M)) % M))
          % M) <<< (28 % M)) % M := rfl
    rw [hval, h41, lit3, lit17, lit28, Nat.shiftLeft_eq u 17, e1, e2, e3, e4,
      Nat.shiftLeft_eq (3 * (u * u + u * 2 ^ 17)) 28, e5]
  · obtain ⟨e1, e2, e3, e4, -, -⟩ := loDen_facts hyge hylt
    have hval : run k t blkC13c 44 =
        ((2 ^ 32 % M) + ((((t 42 * t 42) % M) + ((t 42 <<< (18 % M)) % M))
          % M)) % M := rfl
    rw [hval, h42, lit232, lit18, Nat.shiftLeft_eq y 18, e1, e2, e3, e4]

/-- **Stage C14a**: track `L`'s up-rounded truncated mantissa. -/
theorem blkC14a_spec (k : Nat) (t : RegState) (xL : Nat)
    (h9 : t 9 = xL) (hx : xL < MB) :
    (∀ i, i ≠ 47 → run k t blkC14a i = t i) ∧
    run k t blkC14a 47 = xL / 2 ^ 23 + 2 := by
  have h16 := u16_lt hx
  refine ⟨?_, ?_⟩
  · intro i e47
    simp [run, blkC14a, RegState.set, e47]
  · have hval : run k t blkC14a 47 =
        ((2 % M) + ((t 9 >>> (23 % M)) % M)) % M := rfl
    have e1 : xL / 2 ^ 23 % M = xL / 2 ^ 23 := modId (by
      have h : (2:Nat) ^ 16 < M := by decide
      omega)
    rw [hval, h9, lit2, lit23, Nat.shiftRight_eq_div_pow, e1,
      Nat.add_comm 2 (xL / 2 ^ 23)]
    refine modId ?_
    have h : (2:Nat) ^ 17 < M := by decide
    omega

/-- **Stage C14b**: track `L`'s Padé-upper denominator. -/
theorem blkC14b_spec (k : Nat) (t : RegState) (u : Nat)
    (h47 : t 47 = u) (hu : u ≤ 2 ^ 16 + 1) :
    (∀ i, i ≠ 49 → run k t blkC14b i = t i) ∧
    run k t blkC14b 49 = 393216 + 4 * u := by
  refine ⟨?_, ?_⟩
  · intro i e49
    simp [run, blkC14b, RegState.set, e49]
  · have hval : run k t blkC14b 49 =
        ((393216 % M) + (((4 % M) * t 47) % M)) % M := rfl
    have h4 : 4 * u ≤ 4 * (2 ^ 16 + 1) := Nat.mul_le_mul_left _ hu
    have hM : (4:Nat) * (2 ^ 16 + 1) < M := by decide
    have hM2 : (393216:Nat) + 4 * (2 ^ 16 + 1) < M := by decide
    rw [hval, h47, lit4, lit393216, modId (show 4 * u < M by omega)]
    exact modId (by omega)

/-- **Stage C14c**: track `L`'s Padé-upper dividend, ceiling included. -/
theorem blkC14c_spec (k : Nat) (t : RegState) (u den : Nat)
    (h47 : t 47 = u) (h49 : t 49 = den) (hden : den = 393216 + 4 * u)
    (hu : u ≤ 2 ^ 16 + 1) :
    (∀ i, i ≠ 48 → run k t blkC14c i = t i) ∧
    run k t blkC14c 48 = u * (393216 + u) * 2 ^ 16 + (den - 1) := by
  have hdlo : 393216 ≤ den := by omega
  have hdhi : den < 2 ^ 20 := by
    have h : (393216:Nat) + 4 * (2 ^ 16 + 1) < 2 ^ 20 := by decide
    have h4 : 4 * u ≤ 4 * (2 ^ 16 + 1) := Nat.mul_le_mul_left _ hu
    omega
  have hsum : 393216 + u < 2 ^ 19 := by
    have h : (393216:Nat) + (2 ^ 16 + 1) < 2 ^ 19 := by decide
    omega
  have hprod : u * (393216 + u) < 2 ^ 36 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_lt (show u < 2 ^ 17 by
        have h : (2:Nat) ^ 16 + 1 < 2 ^ 17 := by decide
        omega) hsum) (by decide)
  have hshift : u * (393216 + u) * 2 ^ 16 < 2 ^ 52 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_le hprod (Nat.le_refl _) (by decide)) (by decide)
  refine ⟨?_, ?_⟩
  · intro i e48
    simp [run, blkC14c, RegState.set, e48]
  · -- ⚠ `.sub` against a numeric literal: `denoteOp .sub` puts `M − 1` in
    -- `Nat.add`'s second position, so a `rfl` on the whole shape would
    -- unary-unfold `M − 1`.  Unfold through §6a instead, where every literal
    -- stays a variable.
    have hval : run k t blkC14c 48 =
        (((((t 47 * (((393216 % M) + t 47) % M)) % M) <<< (16 % M)) % M) +
          ((t 49 + (M - (1 % M))) % M)) % M := by
      show run k t ((⟨48, _⟩ : Assign) :: ([] : List Assign)) 48 = _
      rw [run_cons, run_untouched _ _ _ (by decide), set_at,
        evalAdd k t (.bin .shl (.bin .mul (.reg 47)
          (.bin .add (.lit 393216) (.reg 47))) (.lit 16))
          (.bin .sub (.reg 49) (.lit 1)),
        evalShl k t (.bin .mul (.reg 47) (.bin .add (.lit 393216) (.reg 47)))
          (.lit 16),
        evalMul k t (.reg 47) (.bin .add (.lit 393216) (.reg 47)),
        evalAdd k t (.lit 393216) (.reg 47),
        evalSub k t (.reg 49) (.lit 1),
        evalReg k t 47, evalReg k t 49, evalLit k t 393216, evalLit k t 16,
        evalLit k t 1]
    have hdM : den < M := by
      have h : (2:Nat) ^ 20 < M := by decide
      omega
    have e0 : (393216 + u) % M = 393216 + u := modId (by
      have h : (2:Nat) ^ 19 < M := by decide
      omega)
    have e1 : u * (393216 + u) % M = u * (393216 + u) := modId (by
      have h : (2:Nat) ^ 36 < M := by decide
      omega)
    have e2 : u * (393216 + u) * 2 ^ 16 % M = u * (393216 + u) * 2 ^ 16 :=
      modId (by
        have h : (2:Nat) ^ 52 < M := by decide
        omega)
    have e3 : (den + (M - 1)) % M = den - 1 := subExact den 1 (by omega) hdM
    rw [hval, h47, h49, lit393216, lit1, lit16, e0, e1,
      Nat.shiftLeft_eq (u * (393216 + u)) 16, e2, e3]
    exact modId (Nat.lt_of_lt_of_le
      (Nat.add_lt_add hshift (show den - 1 < 2 ^ 20 by omega)) (by decide))

/-- **Stage D1**: the Padé-lower value, rescaled. -/
theorem blkD1_spec (k : Nat) (t : RegState) (q : Nat)
    (h45 : t 45 = q) (hq : q < 2 ^ 32) :
    (∀ i, i ≠ 46 → run k t blkD1 i = t i) ∧
    run k t blkD1 46 = q * 2 ^ 4 := by
  refine ⟨?_, ?_⟩
  · intro i e46
    simp [run, blkD1, RegState.set, e46]
  · have hval : run k t blkD1 46 = ((t 45 <<< (4 % M)) % M) := rfl
    have hlt : q * 2 ^ 4 < M :=
      Nat.lt_of_lt_of_le
        (Nat.mul_lt_mul_of_lt_of_le hq (Nat.le_refl _) (by decide)) (by decide)
    rw [hval, h45, lit4, Nat.shiftLeft_eq]
    exact modId hlt

/-- **Stage D2**: the lower log bound `vL = CL·kU + padeLo`. -/
theorem blkD2_spec (k : Nat) (t : RegState) (kU pl : Nat)
    (h8 : t 8 = kU) (h46 : t 46 = pl) (hkU : kU ≤ KCAP) (hpl : pl < 2 ^ 36) :
    (∀ i, i ≠ 51 → run k t blkD2 i = t i) ∧
    run k t blkD2 51 = CL * kU + pl := by
  have h1 : CL * kU ≤ CL * KCAP := Nat.mul_le_mul_left _ hkU
  have h2 : CL * KCAP + 2 ^ 36 < M := by decide
  refine ⟨?_, ?_⟩
  · intro i e51
    simp [run, blkD2, RegState.set, e51]
  · have hval : run k t blkD2 51 = ((((CL % M) * t 8) % M) + t 46) % M := rfl
    rw [hval, h8, h46, litCL, modId (show CL * kU < M by omega)]
    exact modId (by omega)

/-- **Stage F1a**: the upper log bound and the certificate's `e(n)`. -/
theorem blkF1a_spec (c : Params) (k : Nat) (t : RegState) (kL pu n : Nat)
    (h10 : t 10 = kL) (h50 : t 50 = pu) (h13 : t 13 = n)
    (hkL : kL ≤ KCAP) (hpu : pu < 2 ^ 36) (hesM : c.esplit % M = c.esplit) :
    (∀ i, i ≠ 52 → i ≠ 59 → i ≠ 60 → run k t (blkF1a c) i = t i) ∧
    run k t (blkF1a c) 52 = CU2 * kL + pu ∧
    run k t (blkF1a c) 59 = eOf c n := by
  have h1 : CU2 * kL ≤ CU2 * KCAP := Nat.mul_le_mul_left _ hkL
  have h2 : CU2 * KCAP + 2 ^ 36 < M := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro i e52 e59 e60
    simp [run, blkF1a, RegState.set, e52, e59, e60]
  · have hval : run k t (blkF1a c) 52 =
        ((((CU2 % M) * t 10) % M) + t 50) % M := rfl
    rw [hval, h10, h50, litCU2, modId (show CU2 * kL < M by omega)]
    exact modId (by omega)
  · have hval : run k t (blkF1a c) 59 =
        ((2 % M) + (((14 % M) * (if t 13 < c.esplit % M then 1 else 0)) % M))
          % M := rfl
    have hb := bitLe (n < c.esplit)
    have e1 : 14 * (if n < c.esplit then (1:Nat) else 0) % M
        = 14 * (if n < c.esplit then 1 else 0) := modId (by
      have h : (15:Nat) < M := by decide
      omega)
    rw [hval, h13, hesM, lit2, lit14, e1]
    show (2 + 14 * (if n < c.esplit then (1:Nat) else 0)) % M = eOf c n
    unfold eOf
    refine modId ?_
    have h : (17:Nat) < M := by decide
    omega

/-- **Stage F1a, the exponent index**: exact only in the exponent rounds. -/
theorem blkF1a_spec60 (c : Params) (k : Nat) (t : RegState) (q : Nat)
    (h12 : t 12 = q) (hq : c.tdiv ≤ q) (hqM : q + 1 < M) (htd : c.tdiv < M) :
    run k t (blkF1a c) 60 = q - c.tdiv + 1 := by
  have hval : run k t (blkF1a c) 60 =
      (((t 12 + (M - c.tdiv % M)) % M) + (1 % M)) % M := rfl
  have e1 := subExact q c.tdiv hq (by omega)
  rw [hval, h12, lit1, modId htd, e1]
  exact modId (by omega)

/-- **Stage F1b**: the allowed-exponent bit, the cap gate, the guard. -/
theorem blkF1b_spec (k : Nat) (t : RegState) (b e accU accL xL : Nat)
    (h60 : t 60 = b) (h59 : t 59 = e) (h4 : t 4 = accU) (h5 : t 5 = accL)
    (h9 : t 9 = xL) :
    (∀ i, i ≠ 53 → i ≠ 54 → i ≠ 55 → run k t blkF1b i = t i) ∧
    run k t blkF1b 53 = (if b = e then 1 else 0) ∧
    run k t blkF1b 54 =
      (if accU ≤ ACAP then 1 else 0) * (if accL ≤ ACAP then 1 else 0) ∧
    run k t blkF1b 55 = (if xL ≤ MGUARD then 1 else 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i e53 e54 e55
    simp [run, blkF1b, RegState.set, e53, e54, e55]
  · have hval : run k t blkF1b 53 = (if t 60 = t 59 then 1 else 0) := rfl
    rw [hval, h60, h59]
  · have hval : run k t blkF1b 54 =
        (((if t 4 ≤ ACAP % M then (1:Nat) else 0) *
          (if t 5 ≤ ACAP % M then 1 else 0)) % M) := rfl
    have hprod : (if accU ≤ ACAP then (1:Nat) else 0) *
        (if accL ≤ ACAP then 1 else 0) < M := by
      have b1 := bitLe (accU ≤ ACAP)
      have b2 := bitLe (accL ≤ ACAP)
      have hp : (if accU ≤ ACAP then (1:Nat) else 0) *
          (if accL ≤ ACAP then 1 else 0) ≤ 1 := by
        rcases (show (if accU ≤ ACAP then (1:Nat) else 0) = 0 ∨
          (if accU ≤ ACAP then (1:Nat) else 0) = 1 by omega) with h | h <;>
          rw [h] <;> omega
      have h2 : (2:Nat) ≤ M := by decide
      omega
    rw [hval, h4, h5, litACAP]
    exact modId hprod
  · have hval : run k t blkF1b 55 =
        (if t 9 ≤ MGUARD % M then (1:Nat) else 0) := rfl
    rw [hval, h9, litMGUARD]

/-- **Stage F2, always**: the two comparison registers are bits. -/
theorem blkF2_bits (k : Nat) (t : RegState) (h55 : t 55 ≤ 1) :
    (∀ i, i ≠ 56 → i ≠ 57 → run k t blkF2 i = t i) ∧
    run k t blkF2 56 ≤ 1 ∧ run k t blkF2 57 ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i e56 e57
    simp [run, blkF2, RegState.set, e56, e57]
  · have hval : run k t blkF2 56 =
        (((if t 13 < 120 % M then (1:Nat) else 0) |||
          (if (t 4 * t 60) % M ≤
              ((((t 51 <<< (12 % M)) % M) + (((CU % M) * t 60) % M)) % M)
            then 1 else 0)) % M) := rfl
    rw [hval, or_mod _ _ (bitLe _) (bitLe _)]
    exact bit_or_le _ _ (bitLe _) (bitLe _)
  · have hval : run k t blkF2 57 =
        (((if t 13 < 182 % M then (1:Nat) else 0) |||
          ((t 55 * (if ((((t 52 <<< (12 % M)) % M) + (((CD % M) * t 60) % M))
              % M) ≤ (t 5 * t 60) % M then 1 else 0)) % M)) % M) := rfl
    have hmul : t 55 * (if ((((t 52 <<< (12 % M)) % M) +
        (((CD % M) * t 60) % M)) % M) ≤ (t 5 * t 60) % M
          then (1:Nat) else 0) ≤ 1 := by
      have hb := bitLe (((((t 52 <<< (12 % M)) % M) + (((CD % M) * t 60) % M))
        % M) ≤ (t 5 * t 60) % M)
      rcases (show t 55 = 0 ∨ t 55 = 1 by omega) with h | h <;> rw [h] <;> omega
    have hmulM : t 55 * (if ((((t 52 <<< (12 % M)) % M) +
        (((CD % M) * t 60) % M)) % M) ≤ (t 5 * t 60) % M
          then (1:Nat) else 0) % M = _ := modId (by
      have h2 : (2:Nat) ≤ M := by decide
      omega)
    rw [hval, hmulM, or_mod _ _ (bitLe _) hmul]
    exact bit_or_le _ _ (bitLe _) hmul

/-- **Stage F2, exponent rounds**: the two gated threshold comparisons. -/
theorem blkF2_spec (k : Nat) (t : RegState) (n accU accL b vL vU gd : Nat)
    (h13 : t 13 = n) (h4 : t 4 = accU) (h5 : t 5 = accL) (h60 : t 60 = b)
    (h51 : t 51 = vL) (h52 : t 52 = vU) (h55 : t 55 = gd)
    (hb : b ≤ 16) (hvL : vL < 2 ^ 43) (hvU : vU < 2 ^ 43) (hgd : gd ≤ 1) :
    (∀ i, i ≠ 56 → i ≠ 57 → run k t blkF2 i = t i) ∧
    run k t blkF2 56 =
      ((if n < 120 then 1 else 0) |||
        (if accU * b % M ≤ vL * 2 ^ 12 + CU * b then 1 else 0)) ∧
    run k t blkF2 57 =
      ((if n < 182 then 1 else 0) |||
        gd * (if vU * 2 ^ 12 + CD * b ≤ accL * b % M then 1 else 0)) := by
  have eL : vL * 2 ^ 12 % M = vL * 2 ^ 12 := modId
    (Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_le hvL (Nat.le_refl _) (by decide)) (by decide))
  have eU : vU * 2 ^ 12 % M = vU * 2 ^ 12 := modId
    (Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_le hvU (Nat.le_refl _) (by decide)) (by decide))
  have eCU : CU * b % M = CU * b := modId
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hb) (by decide))
  have eCD : CD * b % M = CD * b := modId
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hb) (by decide))
  have eSL : (vL * 2 ^ 12 + CU * b) % M = vL * 2 ^ 12 + CU * b :=
    modId (Nat.lt_of_lt_of_le
      (Nat.add_lt_add_of_lt_of_le
        (Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_lt_of_le hvL (Nat.le_refl _) (by decide))
          (Nat.le_refl (2 ^ 55)))
        (Nat.mul_le_mul_left _ hb))
      (by decide))
  have eSU : (vU * 2 ^ 12 + CD * b) % M = vU * 2 ^ 12 + CD * b :=
    modId (Nat.lt_of_lt_of_le
      (Nat.add_lt_add_of_lt_of_le
        (Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_lt_of_le hvU (Nat.le_refl _) (by decide))
          (Nat.le_refl (2 ^ 55)))
        (Nat.mul_le_mul_left _ hb))
      (by decide))
  refine ⟨?_, ?_, ?_⟩
  · intro i e56 e57
    simp [run, blkF2, RegState.set, e56, e57]
  · have hval : run k t blkF2 56 =
        (((if t 13 < 120 % M then (1:Nat) else 0) |||
          (if (t 4 * t 60) % M ≤
              ((((t 51 <<< (12 % M)) % M) + (((CU % M) * t 60) % M)) % M)
            then 1 else 0)) % M) := rfl
    rw [hval, h13, h4, h60, h51, lit120, lit12, litCU,
      Nat.shiftLeft_eq vL 12, eL, eCU, eSL]
    exact or_mod _ _ (bitLe _) (bitLe _)
  · have hval : run k t blkF2 57 =
        (((if t 13 < 182 % M then (1:Nat) else 0) |||
          ((t 55 * (if ((((t 52 <<< (12 % M)) % M) + (((CD % M) * t 60) % M))
              % M) ≤ (t 5 * t 60) % M then 1 else 0)) % M)) % M) := rfl
    have hmul : gd * (if vU * 2 ^ 12 + CD * b ≤ accL * b % M
        then (1:Nat) else 0) ≤ 1 := by
      have hbi := bitLe (vU * 2 ^ 12 + CD * b ≤ accL * b % M)
      rcases (show gd = 0 ∨ gd = 1 by omega) with h | h <;> rw [h] <;> omega
    have hmulM : gd * (if vU * 2 ^ 12 + CD * b ≤ accL * b % M
        then (1:Nat) else 0) % M
        = gd * (if vU * 2 ^ 12 + CD * b ≤ accL * b % M then 1 else 0) :=
      modId (by
        have h2 : (2:Nat) ≤ M := by decide
        omega)
    rw [hval, h13, h5, h60, h52, h55, lit182, lit12, litCD,
      Nat.shiftLeft_eq vU 12, eU, eCD, eSU, hmulM]
    exact or_mod _ _ (bitLe _) hmul

/-- **Stage F3a**: the hit. -/
theorem blkF3a_spec (k : Nat) (t : RegState) (cap bal hU hL : Nat)
    (h54 : t 54 = cap) (h53 : t 53 = bal) (h56 : t 56 = hU) (h57 : t 57 = hL)
    (hcap : cap ≤ 1) (hbal : bal ≤ 1) (hhU : hU ≤ 1) (hhL : hL ≤ 1) :
    (∀ i, i ≠ 58 → run k t blkF3a i = t i) ∧
    run k t blkF3a 58 = cap * (bal * (hU * hL)) := by
  have hM2 : (2:Nat) ≤ M := by decide
  have p1 : hU * hL ≤ 1 := by
    rcases (show hU = 0 ∨ hU = 1 by omega) with h | h <;> rw [h] <;> omega
  have p2 : bal * (hU * hL) ≤ 1 := by
    rcases (show bal = 0 ∨ bal = 1 by omega) with h | h <;> rw [h] <;> omega
  have p3 : cap * (bal * (hU * hL)) ≤ 1 := by
    rcases (show cap = 0 ∨ cap = 1 by omega) with h | h <;> rw [h] <;> omega
  refine ⟨?_, ?_⟩
  · intro i e58
    simp [run, blkF3a, RegState.set, e58]
  · have hval : run k t blkF3a 58 =
        ((t 54 * ((t 53 * ((t 56 * t 57) % M)) % M)) % M) := rfl
    rw [hval, h54, h53, h56, h57, modId (show hU * hL < M by omega),
      modId (show bal * (hU * hL) < M by omega)]
    exact modId (by omega)

/-- **Stage F3b**: the pass accumulation. -/
theorem blkF3b_spec (k : Nat) (t : RegState) (ep pass0 hit : Nat)
    (h18 : t 18 = ep) (h6 : t 6 = pass0) (h58 : t 58 = hit)
    (hep : ep ≤ 1) (hpass : pass0 ≤ 1) (hhit : hit ≤ 1) :
    (∀ i, i ≠ 6 → run k t blkF3b i = t i) ∧
    run k t blkF3b 6 = (if ep = 1 then pass0 ||| hit else pass0) := by
  have hM2 : (2:Nat) ≤ M := by decide
  have hor : pass0 ||| hit ≤ 1 := bit_or_le _ _ hpass hhit
  refine ⟨?_, ?_⟩
  · intro i e6
    simp [run, blkF3b, RegState.set, e6]
  · rcases (show ep = 0 ∨ ep = 1 by omega) with h | h <;>
      simp [run, blkF3b, sel, evalExpr, denoteOp, RegState.set, h18, h6, h58, h,
        (by decide : (1:Nat) ^^^ 1 % M = 0), (by decide : (0:Nat) ^^^ 1 % M = 1),
        modId (show pass0 < M by omega), modId (show pass0 ||| hit < M by omega)]

/-- **Stage F3c**: the verdict. -/
theorem blkF3c_spec (k : Nat) (t : RegState) (lastm good pass1 : Nat)
    (h16 : t 16 = lastm) (h0 : t 0 = good) (h6 : t 6 = pass1)
    (hlastm : lastm ≤ 1) (hgood : good ≤ 1) (hpass : pass1 ≤ 1) :
    (∀ i, i ≠ 0 → run k t blkF3c i = t i) ∧
    run k t blkF3c 0 = (if lastm = 1 then good * pass1 else good) := by
  have hM2 : (2:Nat) ≤ M := by decide
  have hgp : good * pass1 ≤ 1 := by
    rcases (show good = 0 ∨ good = 1 by omega) with h | h <;> rw [h] <;> omega
  refine ⟨?_, ?_⟩
  · intro i e0
    simp [run, blkF3c, RegState.set, e0]
  · rcases (show lastm = 0 ∨ lastm = 1 by omega) with h | h <;>
      simp [run, blkF3c, sel, evalExpr, denoteOp, RegState.set, h16, h0, h6, h,
        (by decide : (1:Nat) ^^^ 1 % M = 0), (by decide : (0:Nat) ^^^ 1 % M = 1),
        modId (show good < M by omega), modId (show good * pass1 < M by omega)]

/-- **The epilogue**: the two exact final-sum tests. -/
theorem blkEp_spec (c : Params) (k : Nat) (t : RegState) (good accU accL : Nat)
    (h0 : t 0 = good) (h4 : t 4 = accU) (h5 : t 5 = accL) (hgood : good ≤ 1)
    (hU : c.finU % M = c.finU) (hL : c.finL % M = c.finL) :
    run k t (blkEp c) 0 =
      good * ((if accU ≤ c.finU then 1 else 0) *
        (if c.finL ≤ accL then 1 else 0)) := by
  have hM2 : (2:Nat) ≤ M := by decide
  have b1 := bitLe (accU ≤ c.finU)
  have b2 := bitLe (c.finL ≤ accL)
  have hp : (if accU ≤ c.finU then (1:Nat) else 0) *
      (if c.finL ≤ accL then 1 else 0) ≤ 1 := by
    rcases (show (if accU ≤ c.finU then (1:Nat) else 0) = 0 ∨
      (if accU ≤ c.finU then (1:Nat) else 0) = 1 by omega) with h | h <;>
      rw [h] <;> omega
  have hg : good * ((if accU ≤ c.finU then (1:Nat) else 0) *
      (if c.finL ≤ accL then 1 else 0)) ≤ 1 := by
    rcases (show good = 0 ∨ good = 1 by omega) with h | h <;> rw [h] <;> omega
  have hval : run k t (blkEp c) 0 =
      ((t 0 * (((if t 4 ≤ c.finU % M then (1:Nat) else 0) *
        (if c.finL % M ≤ t 5 then 1 else 0)) % M)) % M) := rfl
  rw [hval, h0, h4, h5, hU, hL, modId (show (if accU ≤ c.finU then (1:Nat)
    else 0) * (if c.finL ≤ accL then 1 else 0) < M by omega)]
  exact modId (by omega)

/-! ## §7 ter The `C` chain, by prefix length

`blkC` is twenty-one sub-blocks and twenty-six assignments, and `st5` is the
corresponding twenty-one-fold `run`.  Naming the intermediate states by the
*number of assignments already run* — `cAt c k m s` — collapses the whole
frame apparatus into two lemmas: one that frames back to `st4` and one that
frames forward to `st5`, each with a single `decide` over a concrete
`List.take` / `List.drop`.  Every intermediate value this port reads is of a
register `blkC` writes exactly once, so the forward frame also serves as the
mid-chain frame. -/

/-- The state after the first `m` assignments of `blkC`. -/
def cAt (c : Params) (k m : Nat) (s : RegState) : RegState :=
  run k (st4 c k s) (blkC.take m)

theorem cAt_zero (c : Params) (k : Nat) (s : RegState) :
    cAt c k 0 s = st4 c k s := rfl

theorem cAt_all (c : Params) (k : Nat) (s : RegState) :
    cAt c k 26 s = st5 c k s := rfl

/-- Backward frame: a register none of the first `m` assignments writes still
holds its `st4` value. -/
theorem cPre (c : Params) (k m : Nat) (s : RegState) (j : Nat)
    (h : ∀ a ∈ blkC.take m, a.dest ≠ j) : cAt c k m s j = st4 c k s j :=
  run_untouched _ _ _ h _

/-- Forward frame: a register none of the remaining assignments writes already
holds its `st5` value. -/
theorem cSuf (c : Params) (k m : Nat) (s : RegState) (j : Nat)
    (h : ∀ a ∈ blkC.drop m, a.dest ≠ j) : st5 c k s j = cAt c k m s j := by
  have hsplit : st5 c k s = run k (cAt c k m s) (blkC.drop m) := by
    show run k (st4 c k s) blkC = _
    unfold cAt
    rw [← run_append, List.take_append_drop]
  rw [hsplit, run_untouched _ _ _ h]

/-! ### The Padé operands, named -/

/-- Track `U`'s truncated mantissa's fractional part. -/
def uUOf (c : Params) (k : Nat) (s : RegState) : Nat := xU1Of c k s / 2 ^ 23

/-- Track `U`'s `17`-bit mantissa. -/
def yUOf (c : Params) (k : Nat) (s : RegState) : Nat := 2 ^ 16 + uUOf c k s

/-- The Padé-lower numerator, already shifted. -/
def pNumUOf (c : Params) (k : Nat) (s : RegState) : Nat :=
  3 * (uUOf c k s * uUOf c k s + uUOf c k s * 2 ^ 17) * 2 ^ 28

/-- The Padé-lower denominator. -/
def pDenUOf (c : Params) (k : Nat) (s : RegState) : Nat :=
  2 ^ 32 + (yUOf c k s * yUOf c k s + yUOf c k s * 2 ^ 18)

/-- The Padé-lower quotient, before the final rescaling. -/
def pQUOf (c : Params) (k : Nat) (s : RegState) : Nat :=
  pNumUOf c k s / pDenUOf c k s

/-- Track `L`'s up-rounded truncated mantissa. -/
def uLOf (c : Params) (k : Nat) (s : RegState) : Nat := xL1Of c k s / 2 ^ 23 + 2

/-- The Padé-upper denominator. -/
def pDenLOf (c : Params) (k : Nat) (s : RegState) : Nat :=
  393216 + 4 * uLOf c k s

/-- The Padé-upper dividend, ceiling included. -/
def pNumLOf (c : Params) (k : Nat) (s : RegState) : Nat :=
  uLOf c k s * (393216 + uLOf c k s) * 2 ^ 16 + (pDenLOf c k s - 1)

/-- The lower log bound. -/
def vLOf (c : Params) (k : Nat) (s : RegState) : Nat :=
  CL * kU1Of c k s + padeLoOf (xU1Of c k s)

/-- The upper log bound. -/
def vUOf (c : Params) (k : Nat) (s : RegState) : Nat :=
  CU2 * kL1Of c k s + padeUpOf (xL1Of c k s)

theorem padeLo_eq (c : Params) (k : Nat) (s : RegState) :
    padeLoOf (xU1Of c k s) = pQUOf c k s * 2 ^ 4 := rfl

theorem padeUp_eq (c : Params) (k : Nat) (s : RegState) :
    padeUpOf (xL1Of c k s) = pNumLOf c k s / pDenLOf c k s := rfl

/-! ## §8 bis The staged values, under the invariant -/

section Staged

variable {c : Params} {k : Nat} {s : RegState}

private theorem divStep_ne (dest : Nat) (op : Op) (a b j : Nat) (t : RegState)
    (h : j ≠ dest) : divStep dest op a b t j = t j := by
  simp [divStep, RegState.set, h]

private theorem litDivStep_ne (dest v b j : Nat) (t : RegState)
    (h : j ≠ dest) : litDivStep dest v b t j = t j := by
  simp [litDivStep, RegState.set, h]

private theorem idx11 (hc : c.Sane) (hk : k < c.len * c.R) :
    idxDivStep c.R k s 11 = k / c.R := by
  have hne : c.R ≠ 0 := by have := hc.RPos; omega
  simp [idxDivStep, RegState.set, denoteOp, hc.RModM,
    Nat.mod_eq_of_lt (hc.loopLtM hk), hne,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self k c.R)
      (hc.loopLtM hk))]

private theorem idx12 (hc : c.Sane) (hk : k < c.len * c.R) :
    idxDivStep c.R k s 12 = k % c.R := by
  have h : k % c.R < M := Nat.lt_trans (Nat.mod_lt _ hc.RPos) hc.RLtM
  have hne : c.R ≠ 0 := by have := hc.RPos; omega
  simp [idxDivStep, RegState.set, denoteOp, hc.RModM,
    Nat.mod_eq_of_lt (hc.loopLtM hk), hne, Nat.mod_eq_of_lt h]

private theorem idxOther (j : Nat) (h11 : j ≠ 11) (h12 : j ≠ 12) :
    idxDivStep c.R k s j = s j := by
  simp [idxDivStep, RegState.set, h11, h12]

/-- Candidate sizing facts, packaged.  The successor track only gets `≤ 2²⁴`:
`Sane.topSmall` bounds `lo + len`, and the top candidate's successor is
exactly that. -/
private theorem candFacts (hc : c.Sane) (hk : k < c.len * c.R) :
    1 ≤ nOf c k ∧ nOf c k < 2 ^ 24 ∧ nOf c k + 1 ≤ 2 ^ 24 ∧
      nOf c k ≤ c.lo + c.len ∧ nOf c k < M ∧ nOf c k + 1 < M := by
  have h1 : 1 ≤ nOf c k := hc.candGe
  have h2 : nOf c k < c.lo + c.len := hc.candLt hk
  have h3 : c.lo + c.len ≤ 2 ^ 24 := hc.topSmall
  have h4 : (2:Nat) ^ 24 < M := two24_lt_M
  exact ⟨h1, by omega, by omega, by omega, by omega, by omega⟩

/-- The two `⌊log₂⌋` brackets both tracks need. -/
private theorem logFacts (hc : c.Sane) (hk : k < c.len * c.R) :
    aUN c k ≤ 24 ∧ 2 ^ aUN c k ≤ nOf c k ∧ nOf c k < 2 ^ (aUN c k + 1) ∧
      aLN c k ≤ 24 ∧ 2 ^ aLN c k ≤ nOf c k + 1 ∧
      nOf c k + 1 < 2 ^ (aLN c k + 1) := by
  obtain ⟨hn1, hn24, hn24', _, _, _⟩ := candFacts hc hk
  obtain ⟨u1, u2, u3⟩ := aOf_bounds (n := nOf c k) hn1 (by omega)
  obtain ⟨v1, v2, v3⟩ := aOf_bounds (n := nOf c k + 1) (by omega) (by omega)
  exact ⟨u1, u2, u3, v1, v2, v3⟩

/-- **Stage 1**: decode, per-candidate reset, and the two exponents. -/
theorem st1_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st1 c k s 0 = s 0 ∧ st1 c k s 4 = s 4 ∧ st1 c k s 5 = s 5 ∧
    st1 c k s 7 = s 7 ∧ st1 c k s 8 = s 8 ∧ st1 c k s 9 = s 9 ∧
    st1 c k s 10 = s 10 ∧
    st1 c k s 12 = qOf c k ∧ st1 c k s 13 = nOf c k ∧
    st1 c k s 14 = dOf c k ∧
    st1 c k s 16 = (if qOf c k = c.R - 1 then 1 else 0) ∧
    st1 c k s 17 = (if qOf c k = c.tdiv then 1 else 0) ∧
    st1 c k s 18 = (if c.tdiv ≤ qOf c k then 1 else 0) ∧
    st1 c k s 1 = m0Of c k s ∧ st1 c k s 2 = phi0Of c k s ∧
    st1 c k s 3 = sq0Of c k s ∧ st1 c k s 6 = pass0Of c k s ∧
    st1 c k s 27 = aUN c k ∧ st1 c k s 28 = 2 ^ aUN c k ∧
    st1 c k s 29 = aLN c k ∧ st1 c k s 30 = 2 ^ aLN c k := by
  obtain ⟨hn1, hn24, hn24', hnbnd, hnM, hn1M⟩ := candFacts hc hk
  have hR := hc.RPos
  have hq : k % c.R < c.R := Nat.mod_lt _ hR
  have hRlt : c.R < 2 ^ 31 := hc.roundsSmall
  have h31 : (2:Nat) ^ 31 < M := two31_lt_M
  have h24M : (2:Nat) ^ 24 < M := two24_lt_M
  have hloM : c.lo % M = c.lo := Nat.mod_eq_of_lt (by
    have h5 := hc.topSmall
    omega)
  have hnMe : (c.lo + k / c.R) % M = c.lo + k / c.R := Nat.mod_eq_of_lt hnM
  have hdMe : (k % c.R + 2) % M = k % c.R + 2 := Nat.mod_eq_of_lt (by omega)
  have hR1M : (c.R - 1) % M = c.R - 1 := Nat.mod_eq_of_lt (by omega)
  have htdM : c.tdiv % M = c.tdiv := Nat.mod_eq_of_lt hc.tdivLtM
  have e1 : idxDivStep c.R k s 1 % M = idxDivStep c.R k s 1 := by
    rw [idxOther 1 (by decide) (by decide)]
    exact Nat.mod_eq_of_lt (hs.word 1)
  have e2 : idxDivStep c.R k s 2 % M = idxDivStep c.R k s 2 := by
    rw [idxOther 2 (by decide) (by decide)]
    exact Nat.mod_eq_of_lt (hs.word 2)
  have e3 : idxDivStep c.R k s 3 % M = idxDivStep c.R k s 3 := by
    rw [idxOther 3 (by decide) (by decide)]
    exact Nat.mod_eq_of_lt (hs.word 3)
  have e6 : idxDivStep c.R k s 6 % M = idxDivStep c.R k s 6 := by
    rw [idxOther 6 (by decide) (by decide)]
    exact Nat.mod_eq_of_lt (hs.word 6)
  obtain ⟨bfr, b13, b14, -, b16, b17, b18, b1, b2, b3, b6⟩ :=
    blkA1_spec c k (idxDivStep c.R k s) (k / c.R) (k % c.R)
      (idx11 hc hk) (idx12 hc hk) hloM hnMe hdMe hR1M htdM e1 e2 e3 e6
  obtain ⟨-, a27, a28, a29, a30⟩ :=
    blkA2_spec k (run k (idxDivStep c.R k s) (blkA1 c)) (nOf c k) b13 hn1 hn24
  -- `blkA1 c` mentions `c`, so its frame cannot go through `decide`; bundle
  -- the ten side conditions into one decidable conjunction instead.
  have fA : ∀ j, (j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3 ∧ j ≠ 6 ∧ j ≠ 13 ∧ j ≠ 14 ∧
      j ≠ 15 ∧ j ≠ 16 ∧ j ≠ 17 ∧ j ≠ 18) →
      run k (idxDivStep c.R k s) (blkA1 c) j = idxDivStep c.R k s j :=
    fun j h => bfr j h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.2.2
  have hst : ∀ j, st1 c k s j =
      run k (run k (idxDivStep c.R k s) (blkA1 c)) blkA2 j := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hst, run_untouched _ _ _ (by decide), fA 0 (by decide),
      idxOther 0 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), fA 4 (by decide),
      idxOther 4 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), fA 5 (by decide),
      idxOther 5 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), fA 7 (by decide),
      idxOther 7 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), fA 8 (by decide),
      idxOther 8 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), fA 9 (by decide),
      idxOther 9 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), fA 10 (by decide),
      idxOther 10 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), fA 12 (by decide)]
    exact idx12 hc hk
  · rw [hst, run_untouched _ _ _ (by decide)]; exact b13
  · rw [hst, run_untouched _ _ _ (by decide)]; exact b14
  · rw [hst, run_untouched _ _ _ (by decide)]; exact b16
  · rw [hst, run_untouched _ _ _ (by decide)]; exact b17
  · rw [hst, run_untouched _ _ _ (by decide)]; exact b18
  · rw [hst, run_untouched _ _ _ (by decide), b1]
    show _ = m0Of c k s
    unfold m0Of qOf nOf
    rw [idxOther 1 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), b2]
    show _ = phi0Of c k s
    unfold phi0Of qOf
    rw [idxOther 2 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), b3]
    show _ = sq0Of c k s
    unfold sq0Of qOf
    rw [idxOther 3 (by decide) (by decide)]
  · rw [hst, run_untouched _ _ _ (by decide), b6]
    show _ = pass0Of c k s
    unfold pass0Of qOf
    rw [idxOther 6 (by decide) (by decide)]
  · rw [hst]; exact a27
  · rw [hst]; exact a28
  · rw [hst]; exact a29
  · rw [hst]; exact a30

/-! ### Bit algebra, hoisted

`omega`'s cost is the size of the local context, and the staged proofs below
carry forty hypotheses; every arithmetic side condition they need is a
top-level lemma with two or three. -/

private theorem bitIf {P : Prop} [Decidable P] (x y : Nat) :
    (if (if P then (1:Nat) else 0) = 1 then x else y) =
      if P then x else y := by
  by_cases h : P <;> simp [h]

/-- The machine's `ep`/`e0` register select against `gRound`'s guard. -/
private theorem mux3' {P Q : Prop} [Decidable P] [Decidable Q] (a b d : Nat) :
    (if (if P then (1:Nat) else 0) = 0 then d
     else if (if Q then (1:Nat) else 0) = 1 then a else b)
      = (if P then (if Q then a else b) else d) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- The position flip between the mask form and `gRound`'s guard. -/
private theorem posFlip {c : Params} {k : Nat} (x y : Nat) :
    (if c.tdiv ≤ qOf c k then x else y)
      = (if qOf c k < c.tdiv then y else x) := by
  by_cases h : c.tdiv ≤ qOf c k
  · rw [if_pos h, if_neg (show ¬ qOf c k < c.tdiv by omega)]
  · rw [if_neg h, if_pos (show qOf c k < c.tdiv by omega)]

private theorem maskMul_eq {P : Prop} [Decidable P] (x : Nat) :
    (if P then (1:Nat) else 0) * x = if P then x else 0 := by
  by_cases h : P <;> simp [h]

/-- A `0/1` mask never raises a bound. -/
private theorem mulBit_le (b x B : Nat) (hb : b ≤ 1) (h : x ≤ B) :
    b * x ≤ B := by
  rcases (show b = 0 ∨ b = 1 by omega) with h1 | h1 <;> rw [h1] <;> omega

/-- Bounds on the reset values. -/
private theorem resetFacts (hc : c.Sane) (hk : k < c.len * c.R)
    (hs : Inv c s) :
    1 ≤ m0Of c k s ∧ m0Of c k s < M ∧ 1 ≤ phi0Of c k s ∧ phi0Of c k s < M ∧
      sq0Of c k s ≤ 1 ∧ m0Of c k s * phi0Of c k s ≤ c.lo + c.len ∧
      pass0Of c k s ≤ 1 := by
  obtain ⟨hn1, hn24, hn24', hnbnd, hnM, hn1M⟩ := candFacts hc hk
  have h1M : (1:Nat) < M := by decide
  unfold m0Of phi0Of sq0Of pass0Of
  by_cases hz : qOf c k = 0 <;> simp only [hz, if_true, if_false, reduceIte]
  · exact ⟨by omega, hnM, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨hs.mPos, hs.word 1, hs.phiPos, hs.word 2, hs.sqLe, hs.prod,
      hs.passLe⟩

/-- **Stage 2**: the two peel quotients. -/
theorem st2_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st2 c k s 19 = m0Of c k s / dOf c k ∧
    st2 c k s 20 = m0Of c k s / dOf c k / dOf c k ∧
    ∀ j, j ≠ 19 → j ≠ 20 → st2 c k s j = st1 c k s j := by
  obtain ⟨hm0p, hm0M, -, -, -, -, -⟩ := resetFacts hc hk hs
  obtain ⟨-, -, -, -, -, -, -, -, -, v14, -, -, -, v1, -, -, -, -, -, -, -⟩ :=
    st1_vals hc hk hs
  have hd0 : dOf c k ≠ 0 := by unfold dOf; omega
  have hq1 : m0Of c k s / dOf c k % M = m0Of c k s / dOf c k :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M)
  have hq2 : m0Of c k s / dOf c k / dOf c k % M
      = m0Of c k s / dOf c k / dOf c k :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M))
  have h19 : divStep 19 .udiv 1 14 (st1 c k s) 19 = m0Of c k s / dOf c k := by
    simp [divStep, RegState.set, denoteOp, v1, v14, hd0, hq1]
  refine ⟨?_, ?_, ?_⟩
  · show divStep 20 .udiv 19 14 (divStep 19 .udiv 1 14 (st1 c k s)) 19 = _
    rw [divStep_ne _ _ _ _ _ _ (by decide)]
    exact h19
  · show divStep 20 .udiv 19 14 (divStep 19 .udiv 1 14 (st1 c k s)) 20 = _
    simp [divStep, RegState.set, denoteOp, v1, v14, hd0, hq1, hq2]
  · intro j hj19 hj20
    show divStep 20 .udiv 19 14 (divStep 19 .udiv 1 14 (st1 c k s)) j
      = st1 c k s j
    rw [divStep_ne _ _ _ _ _ _ hj20, divStep_ne _ _ _ _ _ _ hj19]

/-- Bounds on the peeled values and the two masked terms. -/
private theorem peelFacts (hc : c.Sane) (hk : k < c.len * c.R)
    (hs : Inv c s) :
    1 ≤ m1Of c k s ∧ m1Of c k s < M ∧ 1 ≤ phi1Of c k s ∧ phi1Of c k s < M ∧
      sq1Of c k s ≤ 1 ∧ m1Of c k s * phi1Of c k s ≤ c.lo + c.len ∧
      1 ≤ phiFOf c k s ∧ phiFOf c k s ≤ c.lo + c.len ∧
      phi1Of c k s * (m1Of c k s - 1) < M ∧ tqOf c k s ≤ 2 ^ 44 ∧
      tUOf c k s ≤ 2 ^ 44 + 1 ∧ tLOf c k s ≤ 2 ^ 44 := by
  obtain ⟨hm0p, hm0M, hphi0p, hphi0M, hsq0, hprod0, -⟩ := resetFacts hc hk hs
  have htop : c.lo + c.len ≤ 2 ^ 24 := hc.topSmall
  have h24 : (2:Nat) ^ 24 < M := two24_lt_M
  have hd2 : 2 ≤ dOf c k := by unfold dOf; omega
  have hm1p : 1 ≤ m1Of c k s := by
    unfold m1Of
    split
    · rename_i hdvd
      exact Nat.div_pos
        (Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hdvd)) (by omega)
    · omega
  have hm1M : m1Of c k s < M := by
    unfold m1Of
    split
    · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M
    · exact hm0M
  have hphi1p : 1 ≤ phi1Of c k s := by
    unfold phi1Of
    split
    · have h1 : 1 ≤ dOf c k - 1 := by omega
      calc 1 = 1 * 1 := rfl
        _ ≤ phi0Of c k s * (dOf c k - 1) := Nat.mul_le_mul hphi0p h1
    · exact hphi0p
  have hprod1 : m1Of c k s * phi1Of c k s ≤ c.lo + c.len := by
    unfold m1Of phi1Of
    by_cases hdvd : m0Of c k s % dOf c k = 0
    · simp only [hdvd, if_true, reduceIte]
      have h1 : m0Of c k s / dOf c k * (dOf c k - 1) ≤ m0Of c k s := by
        have h2 : m0Of c k s / dOf c k * (dOf c k - 1)
            ≤ m0Of c k s / dOf c k * dOf c k :=
          Nat.mul_le_mul_left _ (by omega)
        have h3 : m0Of c k s / dOf c k * dOf c k ≤ m0Of c k s :=
          Nat.div_mul_le_self _ _
        omega
      calc m0Of c k s / dOf c k * (phi0Of c k s * (dOf c k - 1))
          = m0Of c k s / dOf c k * (dOf c k - 1) * phi0Of c k s := by
            rw [Nat.mul_assoc, Nat.mul_comm (phi0Of c k s) (dOf c k - 1),
              ← Nat.mul_assoc]
        _ ≤ m0Of c k s * phi0Of c k s := Nat.mul_le_mul_right _ h1
        _ ≤ c.lo + c.len := hprod0
    · simp only [hdvd, if_false, reduceIte]
      exact hprod0
  have hphi1M : phi1Of c k s < M := by
    have h1 : phi1Of c k s ≤ m1Of c k s * phi1Of c k s :=
      Nat.le_mul_of_pos_left _ hm1p
    omega
  have hsq1 : sq1Of c k s ≤ 1 := by
    unfold sq1Of
    split
    · omega
    · exact hsq0
  have hphiFp : 1 ≤ phiFOf c k s := by
    unfold phiFOf
    split
    · rename_i hgt
      have h1 : 1 ≤ m1Of c k s - 1 := by omega
      calc 1 = 1 * 1 := rfl
        _ ≤ phi1Of c k s * (m1Of c k s - 1) := Nat.mul_le_mul hphi1p h1
    · exact hphi1p
  have hphiFbnd : phiFOf c k s ≤ c.lo + c.len := by
    unfold phiFOf
    split
    · have h1 : phi1Of c k s * (m1Of c k s - 1)
          ≤ phi1Of c k s * m1Of c k s := Nat.mul_le_mul_left _ (by omega)
      have h2 : phi1Of c k s * m1Of c k s = m1Of c k s * phi1Of c k s :=
        Nat.mul_comm _ _
      omega
    · have h1 : phi1Of c k s ≤ m1Of c k s * phi1Of c k s :=
        Nat.le_mul_of_pos_left _ hm1p
      omega
  have hphiFM' : phi1Of c k s * (m1Of c k s - 1) < M := by
    have h1 : phi1Of c k s * (m1Of c k s - 1) ≤ phi1Of c k s * m1Of c k s :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : phi1Of c k s * m1Of c k s = m1Of c k s * phi1Of c k s :=
      Nat.mul_comm _ _
    omega
  have htq : tqOf c k s ≤ 2 ^ 44 := Nat.div_le_self _ _
  have htU : tUOf c k s ≤ 2 ^ 44 + 1 := by
    unfold tUOf
    refine mulBit_le _ _ _ hsq1 ?_
    have hb : (if 2 ^ 44 % phiFOf c k s = 0 then (0:Nat) else 1) ≤ 1 := by
      split <;> omega
    exact Nat.add_le_add htq hb
  have htL : tLOf c k s ≤ 2 ^ 44 := mulBit_le _ _ _ hsq1 htq
  exact ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', htq, htU, htL⟩

/-- **Stage 3**: the peel and the totient decode. -/
theorem st3_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st3 c k s 0 = s 0 ∧ st3 c k s 4 = s 4 ∧ st3 c k s 5 = s 5 ∧
    st3 c k s 7 = s 7 ∧ st3 c k s 8 = s 8 ∧ st3 c k s 9 = s 9 ∧
    st3 c k s 10 = s 10 ∧
    st3 c k s 12 = qOf c k ∧ st3 c k s 13 = nOf c k ∧
    st3 c k s 16 = (if qOf c k = c.R - 1 then 1 else 0) ∧
    st3 c k s 17 = (if qOf c k = c.tdiv then 1 else 0) ∧
    st3 c k s 18 = (if c.tdiv ≤ qOf c k then 1 else 0) ∧
    st3 c k s 6 = pass0Of c k s ∧
    st3 c k s 1 = m1Of c k s ∧ st3 c k s 2 = phi1Of c k s ∧
    st3 c k s 3 = sq1Of c k s ∧ st3 c k s 22 = phiFOf c k s ∧
    st3 c k s 27 = aUN c k ∧ st3 c k s 28 = 2 ^ aUN c k ∧
    st3 c k s 29 = aLN c k ∧ st3 c k s 30 = 2 ^ aLN c k := by
  obtain ⟨hm0p, hm0M, hphi0p, hphi0M, hsq0, hprod0, hpass0⟩ :=
    resetFacts hc hk hs
  obtain ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', htq, htU, htL⟩ := peelFacts hc hk hs
  obtain ⟨v0, v4, v5, v7, v8, v9, v10, v12, v13, v14, v16, v17, v18, v1, v2,
    v3, v6, v27, v28, v29, v30⟩ := st1_vals hc hk hs
  obtain ⟨w19, w20, wfr⟩ := st2_vals hc hk hs
  have hd0 : 0 < dOf c k := by unfold dOf; omega
  have hd1 : dOf c k - 1 = qOf c k + 1 := by unfold dOf; omega
  have hqlt : qOf c k < c.R := by unfold qOf; exact Nat.mod_lt _ hc.RPos
  have hq1M : (qOf c k + 1) % M = qOf c k + 1 := Nat.mod_eq_of_lt (by
    have h1 : c.R < 2 ^ 31 := hc.roundsSmall
    have h2 : (2:Nat) ^ 31 < M := two31_lt_M
    omega)
  have hphi0bnd : phi0Of c k s ≤ c.lo + c.len := by
    have h2 : phi0Of c k s ≤ m0Of c k s * phi0Of c k s :=
      Nat.le_mul_of_pos_left _ hm0p
    omega
  have hprodM : (phi0Of c k s * (qOf c k + 1)) % M
      = phi0Of c k s * (qOf c k + 1) := Nat.mod_eq_of_lt (by
    have h3 : phi0Of c k s * (qOf c k + 1) ≤ (c.lo + c.len) * c.R :=
      Nat.mul_le_mul hphi0bnd (by omega)
    have h4 : (c.lo + c.len) * c.R ≤ 2 ^ 24 * 2 ^ 31 :=
      Nat.mul_le_mul hc.topSmall (Nat.le_of_lt hc.roundsSmall)
    have h5 : (2:Nat) ^ 24 * 2 ^ 31 < M := by decide
    omega)
  have hprodM' : (phi1Of c k s * (m1Of c k s - 1)) % M
      = phi1Of c k s * (m1Of c k s - 1) := Nat.mod_eq_of_lt hphiFM'
  -- stage B1 on `st2`
  obtain ⟨-, p21, p3⟩ :=
    blkB1_spec k (st2 c k s) (m0Of c k s) (sq0Of c k s) (dOf c k)
      (by rw [wfr 1 (by decide) (by decide)]; exact v1)
      (by rw [wfr 3 (by decide) (by decide)]; exact v3)
      (by rw [wfr 14 (by decide) (by decide)]; exact v14)
      w19 w20 hd0 hm0M hsq0
  -- stage B2
  obtain ⟨-, r2, r1⟩ :=
    blkB2_spec k (run k (st2 c k s) blkB1) (m0Of c k s) (phi0Of c k s)
      (qOf c k) (dOf c k)
      (by rw [run_untouched _ _ _ (by decide), wfr 1 (by decide) (by decide)]
          exact v1)
      (by rw [run_untouched _ _ _ (by decide), wfr 2 (by decide) (by decide)]
          exact v2)
      (by rw [run_untouched _ _ _ (by decide), wfr 12 (by decide) (by decide)]
          exact v12)
      (by rw [run_untouched _ _ _ (by decide)]; exact w19)
      p21 rfl hq1M (by rw [← hd1]; exact hprodM) hm0M hphi0M
  rw [hd1] at r2
  -- stage B3
  obtain ⟨-, u22⟩ :=
    blkB3_spec k (run k (run k (st2 c k s) blkB1) blkB2) (m1Of c k s)
      (phi1Of c k s) (by rw [r1]; rfl) (by rw [r2]; rfl) hm1M hphi1M hprodM'
      hm1p
  have hBeq : st3 c k s = run k (st2 c k s) blkB := by
    show run k (run k (run k (st2 c k s) blkB1) blkB2) blkB3 = _
    rw [show blkB = blkB1 ++ blkB2 ++ blkB3 from rfl, run_append, run_append]
  have hfr : ∀ j, (∀ a ∈ blkB, a.dest ≠ j) → j ≠ 19 → j ≠ 20 →
      st3 c k s j = st1 c k s j := by
    intro j hj h19 h20
    rw [hBeq, run_untouched _ _ _ hj]
    exact wfr j h19 h20
  have hst : ∀ j, st3 c k s j
      = run k (run k (run k (st2 c k s) blkB1) blkB2) blkB3 j := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hfr 0 (by decide) (by decide) (by decide)]; exact v0
  · rw [hfr 4 (by decide) (by decide) (by decide)]; exact v4
  · rw [hfr 5 (by decide) (by decide) (by decide)]; exact v5
  · rw [hfr 7 (by decide) (by decide) (by decide)]; exact v7
  · rw [hfr 8 (by decide) (by decide) (by decide)]; exact v8
  · rw [hfr 9 (by decide) (by decide) (by decide)]; exact v9
  · rw [hfr 10 (by decide) (by decide) (by decide)]; exact v10
  · rw [hfr 12 (by decide) (by decide) (by decide)]; exact v12
  · rw [hfr 13 (by decide) (by decide) (by decide)]; exact v13
  · rw [hfr 16 (by decide) (by decide) (by decide)]; exact v16
  · rw [hfr 17 (by decide) (by decide) (by decide)]; exact v17
  · rw [hfr 18 (by decide) (by decide) (by decide)]; exact v18
  · rw [hfr 6 (by decide) (by decide) (by decide)]; exact v6
  · rw [hst, run_untouched _ _ _ (by decide), r1]; rfl
  · rw [hst, run_untouched _ _ _ (by decide), r2]; rfl
  · rw [hst, run_untouched _ _ _ (by decide),
      run_untouched _ _ _ (by decide), p3]
    rfl
  · rw [hst]; exact u22
  · rw [hfr 27 (by decide) (by decide) (by decide)]; exact v27
  · rw [hfr 28 (by decide) (by decide) (by decide)]; exact v28
  · rw [hfr 29 (by decide) (by decide) (by decide)]; exact v29
  · rw [hfr 30 (by decide) (by decide) (by decide)]; exact v30

/-- **Stage 4**: the term division. -/
theorem st4_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st4 c k s 23 = tqOf c k s ∧
    ∀ j, j ≠ 23 → st4 c k s j = st3 c k s j := by
  obtain ⟨-, -, -, -, -, -, hphiFp, hphiFbnd, -, htq, -, -⟩ :=
    peelFacts hc hk hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, v22, -, -, -, -⟩ :=
    st3_vals hc hk hs
  have hne : phiFOf c k s ≠ 0 := by omega
  constructor
  · show litDivStep 23 (2 ^ 44) 22 (st3 c k s) 23 = tqOf c k s
    have hgoal : litDivStep 23 (2 ^ 44) 22 (st3 c k s) 23
        = (denoteOp .udiv (2 ^ 44 % M) (st3 c k s 22)).getD 0 := rfl
    rw [hgoal, v22, lit244]
    simp only [denoteOp, if_neg hne, Option.getD_some]
    show 2 ^ 44 / phiFOf c k s % M = tqOf c k s
    unfold tqOf
    refine Nat.mod_eq_of_lt ?_
    have h1 : (2:Nat) ^ 44 < M := by decide
    have h2 : 2 ^ 44 / phiFOf c k s ≤ 2 ^ 44 := Nat.div_le_self _ _
    omega
  · intro j hj
    show litDivStep 23 (2 ^ 44) 22 (st3 c k s) j = st3 c k s j
    rw [litDivStep_ne _ _ _ _ _ hj]

/-! ### The two mantissa tracks stay in band -/

private theorem mbLtM : MB < M := by decide

/-- The mantissa advance's width budget at a candidate that may sit exactly
on `2²⁴`. -/
private theorem advX_le_lt {n a x : Nat} (hx : x < MB) (hn : n ≤ 2 ^ 24) :
    advX n a x < M := by
  unfold advX
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (advX_prod_le hx hn)

/-- **Track `U` stays in band, and the `KCAP` clamp is inert.** -/
private theorem mantFactsU (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    MB ≤ x2UOf c k s ∧ x2UOf c k s < 2 ^ 41 ∧
      xUAOf c k s < MB ∧ xUIOf c k < MB ∧ xU1Of c k s < MB ∧
      kU1Of c k s ≤ KCAP := by
  obtain ⟨ha24, hpa, hpa', -, -, -⟩ := logFacts hc hk
  have hband : MB ≤ x2UOf c k s ∧ x2UOf c k s < 2 ^ 41 :=
    advX_band hs.xULt hpa hpa'
  obtain ⟨hr1, hr2⟩ := advRenorm_band hband.1 hband.2
  have hMB : MB = 2 ^ 39 := rfl
  have hA : xUAOf c k s < MB := by
    unfold xUAOf gUOf
    simp only [hMB] at hr1 hr2 ⊢
    omega
  have hI : xUIOf c k < MB := by
    unfold xUIOf
    simp only [hMB]
    exact xI_lt hpa hpa' (by omega)
  refine ⟨hband.1, hband.2, hA, hI, ?_, ?_⟩
  · unfold xU1Of
    split
    · exact hs.xULt
    · split
      · exact hI
      · exact hA
  · unfold kU1Of
    split
    · exact hs.kULe
    · split
      · simp only [KCAP]; omega
      · split
        · assumption
        · exact Nat.le_refl _

/-- **Track `L` stays in band, and the `KCAP` clamp is inert.** -/
private theorem mantFactsL (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    MB ≤ x2LOf c k s ∧ x2LOf c k s < 2 ^ 41 ∧
      xLAOf c k s < MB ∧ xLIOf c k < MB ∧ xL1Of c k s < MB ∧
      kL1Of c k s ≤ KCAP := by
  obtain ⟨-, -, -, ha24, hpa, hpa'⟩ := logFacts hc hk
  have hband : MB ≤ x2LOf c k s ∧ x2LOf c k s < 2 ^ 41 :=
    advX_band hs.xLLt hpa hpa'
  obtain ⟨hr1, hr2⟩ := advRenorm_band hband.1 hband.2
  have hMB : MB = 2 ^ 39 := rfl
  have hA : xLAOf c k s < MB := by
    unfold xLAOf gLOf
    simp only [hMB] at hr1 hr2 ⊢
    omega
  have hI : xLIOf c k < MB := by
    unfold xLIOf
    simp only [hMB]
    exact xI_lt hpa hpa' (by omega)
  refine ⟨hband.1, hband.2, hA, hI, ?_, ?_⟩
  · unfold xL1Of
    split
    · exact hs.xLLt
    · split
      · exact hI
      · exact hA
  · unfold kL1Of
    split
    · exact hs.kLLe
    · split
      · simp only [KCAP]; omega
      · split
        · assumption
        · exact Nat.le_refl _

/-- The unclamped exponents stay inside a word. -/
private theorem kNFacts (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    kUNOf c k s < M ∧ kLNOf c k s < M := by
  obtain ⟨haU, -, -, haL, -, -⟩ := logFacts hc hk
  have hU := hs.kULe
  have hL := hs.kLLe
  have hgU := bitLe (2 ^ 40 ≤ x2UOf c k s)
  have hgL := bitLe (2 ^ 40 ≤ x2LOf c k s)
  have hcap : KCAP = 1024 := rfl
  have hM : (1050:Nat) < M := by decide
  constructor
  · unfold kUNOf gUOf
    simp only [hcap] at hU
    omega
  · unfold kLNOf gLOf
    simp only [hcap] at hL
    omega

/-- Every width the two Padé divisions and the two comparisons need. -/
private theorem padeFacts (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    uUOf c k s < 2 ^ 16 ∧ 2 ^ 16 ≤ yUOf c k s ∧ yUOf c k s < 2 ^ 17 ∧
      2 ^ 33 ≤ pDenUOf c k s ∧ pDenUOf c k s < 2 ^ 37 ∧
      pQUOf c k s < 2 ^ 32 ∧ padeLoOf (xU1Of c k s) < 2 ^ 36 ∧
      uLOf c k s ≤ 2 ^ 16 + 1 ∧ 393216 ≤ pDenLOf c k s ∧
      pDenLOf c k s < 2 ^ 20 ∧ pNumLOf c k s ≤ 2 ^ 52 + 2 ^ 20 ∧
      padeUpOf (xL1Of c k s) < 2 ^ 36 ∧
      vLOf c k s < 2 ^ 43 ∧ vUOf c k s < 2 ^ 43 := by
  obtain ⟨-, -, -, -, hxU, hkU⟩ := mantFactsU hc hk hs
  obtain ⟨-, -, -, -, hxL, hkL⟩ := mantFactsL hc hk hs
  have hu : uUOf c k s < 2 ^ 16 := u16_lt hxU
  have hyge : 2 ^ 16 ≤ yUOf c k s := Nat.le_add_right _ _
  have hylt : yUOf c k s < 2 ^ 17 := by
    unfold yUOf
    have h : (2:Nat) ^ 16 + 2 ^ 16 = 2 ^ 17 := by decide
    omega
  obtain ⟨-, -, -, -, hdlo, hdhi⟩ := loDen_facts hyge hylt
  obtain ⟨-, -, -, -, -, -, hnle⟩ := loNum_facts hu
  have hpq : pQUOf c k s < 2 ^ 32 := by
    unfold pQUOf
    have h1 : pNumUOf c k s / pDenUOf c k s ≤ pNumUOf c k s / 2 ^ 33 :=
      Nat.div_le_div_left hdlo (by decide)
    have h2 : pNumUOf c k s / 2 ^ 33 ≤ (3 * 2 ^ 34 * 2 ^ 28) / 2 ^ 33 :=
      Nat.div_le_div_right hnle
    have h3 : (3 * 2 ^ 34 * 2 ^ 28) / 2 ^ 33 = 3 * 2 ^ 29 := by decide
    have h4 : (3:Nat) * 2 ^ 29 < 2 ^ 32 := by decide
    omega
  have hpl : padeLoOf (xU1Of c k s) < 2 ^ 36 := by
    rw [padeLo_eq]
    have h1 : pQUOf c k s * 2 ^ 4 < 2 ^ 32 * 2 ^ 4 :=
      Nat.mul_lt_mul_of_lt_of_le hpq (Nat.le_refl _) (by decide)
    have h2 : (2:Nat) ^ 32 * 2 ^ 4 ≤ 2 ^ 36 := by decide
    omega
  have huL : uLOf c k s ≤ 2 ^ 16 + 1 := by
    unfold uLOf
    have h := u16_lt hxL
    omega
  have hdLlo : 393216 ≤ pDenLOf c k s := Nat.le_add_right _ _
  have hdLhi : pDenLOf c k s < 2 ^ 20 := by
    unfold pDenLOf
    have h1 : 4 * uLOf c k s ≤ 4 * (2 ^ 16 + 1) := Nat.mul_le_mul_left _ huL
    have h2 : (393216:Nat) + 4 * (2 ^ 16 + 1) < 2 ^ 20 := by decide
    omega
  have hsum : 393216 + uLOf c k s < 2 ^ 19 := by
    have h : (393216:Nat) + (2 ^ 16 + 1) < 2 ^ 19 := by decide
    omega
  have hprod : uLOf c k s * (393216 + uLOf c k s) < 2 ^ 36 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_lt (show uLOf c k s < 2 ^ 17 by
        have h : (2:Nat) ^ 16 + 1 < 2 ^ 17 := by decide
        omega) hsum) (by decide)
  have hshift : uLOf c k s * (393216 + uLOf c k s) * 2 ^ 16 < 2 ^ 52 :=
    Nat.lt_of_lt_of_le
      (Nat.mul_lt_mul_of_lt_of_le hprod (Nat.le_refl _) (by decide)) (by decide)
  have hnL : pNumLOf c k s ≤ 2 ^ 52 + 2 ^ 20 := by
    unfold pNumLOf
    exact Nat.add_le_add (Nat.le_of_lt hshift)
      (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ 1) hdLhi))
  have hpu : padeUpOf (xL1Of c k s) < 2 ^ 36 := by
    rw [padeUp_eq]
    have h1 : pNumLOf c k s / pDenLOf c k s ≤ pNumLOf c k s / 2 ^ 18 :=
      Nat.div_le_div_left (by
        have h : (2:Nat) ^ 18 ≤ 393216 := by decide
        omega) (by decide)
    have h2 : pNumLOf c k s / 2 ^ 18 ≤ (2 ^ 52 + 2 ^ 20) / 2 ^ 18 :=
      Nat.div_le_div_right hnL
    have h3 : ((2:Nat) ^ 52 + 2 ^ 20) / 2 ^ 18 < 2 ^ 36 := by decide
    omega
  have hvL : vLOf c k s < 2 ^ 43 := by
    unfold vLOf
    have h1 : CL * kU1Of c k s ≤ CL * KCAP := Nat.mul_le_mul_left _ hkU
    have h2 : CL * KCAP + 2 ^ 36 < 2 ^ 43 := by decide
    omega
  have hvU : vUOf c k s < 2 ^ 43 := by
    unfold vUOf
    have h1 : CU2 * kL1Of c k s ≤ CU2 * KCAP := Nat.mul_le_mul_left _ hkL
    have h2 : CU2 * KCAP + 2 ^ 36 < 2 ^ 43 := by decide
    omega
  exact ⟨hu, hyge, hylt, hdlo, hdhi, hpq, hpl, huL, hdLlo, hdLhi, hnL, hpu,
    hvL, hvU⟩

set_option maxHeartbeats 2000000 in
/-- **Stage 5**: the two accumulators, the two mantissae, the two exponents,
and the two Padé operand pairs.  Twenty-one block specifications and forty
frames in one declaration, so the default heartbeat budget is not enough. -/
theorem st5_vals (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    st5 c k s 0 = s 0 ∧ st5 c k s 1 = m1Of c k s ∧
    st5 c k s 2 = phi1Of c k s ∧ st5 c k s 3 = sq1Of c k s ∧
    st5 c k s 6 = pass0Of c k s ∧
    st5 c k s 12 = qOf c k ∧ st5 c k s 13 = nOf c k ∧
    st5 c k s 16 = (if qOf c k = c.R - 1 then 1 else 0) ∧
    st5 c k s 17 = (if qOf c k = c.tdiv then 1 else 0) ∧
    st5 c k s 18 = (if c.tdiv ≤ qOf c k then 1 else 0) ∧
    st5 c k s 4 = accU1Of c k s ∧ st5 c k s 5 = accL1Of c k s ∧
    st5 c k s 7 = xU1Of c k s ∧ st5 c k s 8 = kU1Of c k s ∧
    st5 c k s 9 = xL1Of c k s ∧ st5 c k s 10 = kL1Of c k s ∧
    st5 c k s 43 = pNumUOf c k s ∧ st5 c k s 44 = pDenUOf c k s ∧
    st5 c k s 47 = uLOf c k s ∧ st5 c k s 48 = pNumLOf c k s ∧
    st5 c k s 49 = pDenLOf c k s := by
  obtain ⟨hn1, hn24, hn24', hnbnd, hnM, hn1M⟩ := candFacts hc hk
  obtain ⟨haU24, haUlo, haUhi, haL24, haLlo, haLhi⟩ := logFacts hc hk
  obtain ⟨hm1p, hm1M, hphi1p, hphi1M, hsq1, hprod1, hphiFp, hphiFbnd,
    hphiFM', htq, htU, htL⟩ := peelFacts hc hk hs
  obtain ⟨hx2Ulo, hx2Uhi, hxUA, hxUI, hxU1, hkU1⟩ := mantFactsU hc hk hs
  obtain ⟨hx2Llo, hx2Lhi, hxLA, hxLI, hxL1, hkL1⟩ := mantFactsL hc hk hs
  obtain ⟨hkUNM, hkLNM⟩ := kNFacts hc hk hs
  obtain ⟨hu, hyge, hylt, hdUlo, hdUhi, hpq, hpl, huL, hdLlo, hdLhi, hnL,
    hpu, hvLb, hvUb⟩ := padeFacts hc hk hs
  obtain ⟨w0, w4, w5, w7, w8, w9, w10, w12, w13, w16, w17, w18, w6, w1, w2,
    w3, w22, w27, w28, w29, w30⟩ := st3_vals hc hk hs
  obtain ⟨w23, wfr⟩ := st4_vals hc hk hs
  -- widths, hoisted out of the forty-hypothesis context below
  have htqM : tqOf c k s + 1 < M :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_right htq 1) (by decide)
  have htUM : tUOf c k s < M := Nat.lt_of_le_of_lt htU (by decide)
  have htLM : tLOf c k s < M := Nat.lt_of_le_of_lt htL (by decide)
  have haUM : aUN c k < M := Nat.lt_of_le_of_lt haU24 (by decide)
  have haLM : aLN c k < M := Nat.lt_of_le_of_lt haL24 (by decide)
  have hxUIM : xUIOf c k < M := Nat.lt_trans hxUI mbLtM
  have hxUAM : xUAOf c k s < M := Nat.lt_trans hxUA mbLtM
  have hxLIM : xLIOf c k < M := Nat.lt_trans hxLI mbLtM
  have hxLAM : xLAOf c k s < M := Nat.lt_trans hxLA mbLtM
  -- the incoming state
  have z0 : st4 c k s 0 = s 0 := by rw [wfr 0 (by decide)]; exact w0
  have z1 : st4 c k s 1 = m1Of c k s := by rw [wfr 1 (by decide)]; exact w1
  have z2 : st4 c k s 2 = phi1Of c k s := by rw [wfr 2 (by decide)]; exact w2
  have z3 : st4 c k s 3 = sq1Of c k s := by rw [wfr 3 (by decide)]; exact w3
  have z4 : st4 c k s 4 = s 4 := by rw [wfr 4 (by decide)]; exact w4
  have z5 : st4 c k s 5 = s 5 := by rw [wfr 5 (by decide)]; exact w5
  have z6 : st4 c k s 6 = pass0Of c k s := by rw [wfr 6 (by decide)]; exact w6
  have z7 : st4 c k s 7 = s 7 := by rw [wfr 7 (by decide)]; exact w7
  have z8 : st4 c k s 8 = s 8 := by rw [wfr 8 (by decide)]; exact w8
  have z9 : st4 c k s 9 = s 9 := by rw [wfr 9 (by decide)]; exact w9
  have z10 : st4 c k s 10 = s 10 := by rw [wfr 10 (by decide)]; exact w10
  have z12 : st4 c k s 12 = qOf c k := by rw [wfr 12 (by decide)]; exact w12
  have z13 : st4 c k s 13 = nOf c k := by rw [wfr 13 (by decide)]; exact w13
  have z16 : st4 c k s 16 = (if qOf c k = c.R - 1 then 1 else 0) := by
    rw [wfr 16 (by decide)]; exact w16
  have z17 : st4 c k s 17 = (if qOf c k = c.tdiv then 1 else 0) := by
    rw [wfr 17 (by decide)]; exact w17
  have z18 : st4 c k s 18 = (if c.tdiv ≤ qOf c k then 1 else 0) := by
    rw [wfr 18 (by decide)]; exact w18
  have z22 : st4 c k s 22 = phiFOf c k s := by rw [wfr 22 (by decide)]; exact w22
  have z27 : st4 c k s 27 = aUN c k := by rw [wfr 27 (by decide)]; exact w27
  have z28 : st4 c k s 28 = 2 ^ aUN c k := by rw [wfr 28 (by decide)]; exact w28
  have z29 : st4 c k s 29 = aLN c k := by rw [wfr 29 (by decide)]; exact w29
  have z30 : st4 c k s 30 = 2 ^ aLN c k := by rw [wfr 30 (by decide)]; exact w30
  -- the two frames of the chain, specialised
  have P : ∀ m j, (∀ a ∈ blkC.take m, a.dest ≠ j) →
      cAt c k m s j = st4 c k s j := fun m j h => cPre c k m s j h
  have Q : ∀ m n j, (∀ a ∈ blkC.drop m, a.dest ≠ j) →
      (∀ a ∈ blkC.drop n, a.dest ≠ j) → cAt c k m s j = cAt c k n s j :=
    fun m n j hm hn => (cSuf c k m s j hm).symm.trans (cSuf c k n s j hn)
  -- C1a: the exactness bit
  obtain ⟨-, V24⟩ := blkC1a_spec k (cAt c k 0 s) (phiFOf c k s)
    (by rw [cAt_zero]; exact z22) (by rw [cAt_zero]; exact w23) hphiFp
  have A24 : cAt c k 1 s 24 = (if 2 ^ 44 % phiFOf c k s = 0 then 1 else 0) :=
    V24
  -- C1b: the two masked terms
  obtain ⟨-, V25, V26⟩ := blkC1b_spec k (cAt c k 1 s) (sq1Of c k s)
    (tqOf c k s) (2 ^ 44 % phiFOf c k s)
    (by rw [P 1 3 (by decide)]; exact z3)
    (by rw [P 1 23 (by decide)]; exact w23)
    A24 hsq1 htqM
  have A25 : cAt c k 3 s 25 = tUOf c k s := V25
  have A26 : cAt c k 3 s 26 = tLOf c k s := V26
  -- C2: the two accumulator steps
  obtain ⟨-, V4, V5⟩ := blkC2_spec k (cAt c k 3 s) (s 4) (s 5)
    (if qOf c k = c.tdiv then 1 else 0) (tUOf c k s) (tLOf c k s)
    (by rw [P 3 4 (by decide)]; exact z4)
    (by rw [P 3 5 (by decide)]; exact z5)
    (by rw [P 3 17 (by decide)]; exact z17)
    A25 A26 (bitLe _) htUM htLM
  have A4 : cAt c k 5 s 4 = accU1Of c k s := by
    have h : cAt c k 5 s 4 =
        (s 4 + if (if qOf c k = c.tdiv then (1:Nat) else 0) = 1
          then tUOf c k s else 0) % M := V4
    rw [h, bitIf]
    rfl
  have A5 : cAt c k 5 s 5 = accL1Of c k s := by
    have h : cAt c k 5 s 5 =
        (s 5 + if (if qOf c k = c.tdiv then (1:Nat) else 0) = 1
          then tLOf c k s else 0) % M := V5
    rw [h, bitIf]
    rfl
  -- C3a/C3b: track `U`'s advance and renormalisation bit
  obtain ⟨-, V31⟩ := blkC3a_spec k (cAt c k 5 s) (s 7) (nOf c k) (aUN c k)
    (by rw [P 5 7 (by decide)]; exact z7)
    (by rw [P 5 13 (by decide)]; exact z13)
    (by rw [P 5 27 (by decide)]; exact z27)
    hs.xULt hn24
  have A31 : cAt c k 6 s 31 = x2UOf c k s := V31
  obtain ⟨-, V32⟩ := blkC3b_spec k (cAt c k 6 s) (x2UOf c k s) A31
  have A32 : cAt c k 7 s 32 = gUOf c k s := V32
  -- C4/C5: track `U`'s mantissa
  obtain ⟨-, V33, V34⟩ := blkC4_spec k (cAt c k 7 s) (x2UOf c k s)
    (gUOf c k s) (nOf c k) (aUN c k)
    (by rw [Q 7 6 31 (by decide) (by decide)]; exact A31) A32
    (by rw [P 7 13 (by decide)]; exact z13)
    (by rw [P 7 28 (by decide)]; exact z28)
    (by rw [P 7 27 (by decide)]; exact z27)
    rfl hx2Ulo hx2Uhi haUlo haUhi haU24
  have A33 : cAt c k 9 s 33 = xUAOf c k s := V33
  have A34 : cAt c k 9 s 34 = xUIOf c k := V34
  obtain ⟨-, V7⟩ := blkC5_spec k (cAt c k 9 s)
    (if c.tdiv ≤ qOf c k then 1 else 0) (if qOf c k = c.tdiv then 1 else 0)
    (xUIOf c k) (xUAOf c k s) (s 7)
    (by rw [P 9 18 (by decide)]; exact z18)
    (by rw [P 9 17 (by decide)]; exact z17)
    A34 A33
    (by rw [P 9 7 (by decide)]; exact z7)
    (bitLe _) (bitLe _) hxUIM hxUAM (hs.word 7)
  have A7 : cAt c k 10 s 7 = xU1Of c k s := by
    have h : cAt c k 10 s 7 =
        (if (if c.tdiv ≤ qOf c k then (1:Nat) else 0) = 0 then s 7
         else if (if qOf c k = c.tdiv then (1:Nat) else 0) = 1
           then xUIOf c k else xUAOf c k s) := V7
    rw [h, mux3', posFlip]
    rfl
  -- C6/C7: track `U`'s exponent
  obtain ⟨-, V35⟩ := blkC6_spec k (cAt c k 10 s) (s 8) (aUN c k) (gUOf c k s)
    (by rw [P 10 8 (by decide)]; exact z8)
    (by rw [P 10 27 (by decide)]; exact z27)
    (by rw [Q 10 7 32 (by decide) (by decide)]; exact A32)
    hkUNM
  have A35 : cAt c k 11 s 35 = kUNOf c k s := V35
  obtain ⟨-, V8⟩ := blkC7_spec k (cAt c k 11 s)
    (if c.tdiv ≤ qOf c k then 1 else 0) (if qOf c k = c.tdiv then 1 else 0)
    (aUN c k) (kUNOf c k s) (s 8)
    (by rw [P 11 18 (by decide)]; exact z18)
    (by rw [P 11 17 (by decide)]; exact z17)
    (by rw [P 11 27 (by decide)]; exact z27)
    A35
    (by rw [P 11 8 (by decide)]; exact z8)
    (bitLe _) (bitLe _) haUM hkUNM (hs.word 8)
  have A8 : cAt c k 12 s 8 = kU1Of c k s := by
    have h : cAt c k 12 s 8 =
        (if (if c.tdiv ≤ qOf c k then (1:Nat) else 0) = 0 then s 8
         else if (if qOf c k = c.tdiv then (1:Nat) else 0) = 1 then aUN c k
         else if kUNOf c k s ≤ KCAP then kUNOf c k s else KCAP) := V8
    rw [h, mux3', posFlip]
    rfl
  -- C8a/C8b: track `L`'s advance and renormalisation bit
  obtain ⟨-, V36⟩ := blkC8a_spec' k (cAt c k 12 s) (s 9) (nOf c k) (aLN c k)
    (by rw [P 12 9 (by decide)]; exact z9)
    (by rw [P 12 13 (by decide)]; exact z13)
    (by rw [P 12 29 (by decide)]; exact z29)
    hs.xLLt hn24'
  have A36 : cAt c k 13 s 36 = x2LOf c k s := V36
  obtain ⟨-, V37⟩ := blkC8b_spec k (cAt c k 13 s) (x2LOf c k s) A36
  have A37 : cAt c k 14 s 37 = gLOf c k s := V37
  -- C9/C10: track `L`'s mantissa
  obtain ⟨-, V38, V39⟩ := blkC9_spec k (cAt c k 14 s) (x2LOf c k s)
    (gLOf c k s) (nOf c k) (aLN c k)
    (by rw [Q 14 13 36 (by decide) (by decide)]; exact A36) A37
    (by rw [P 14 13 (by decide)]; exact z13)
    (by rw [P 14 30 (by decide)]; exact z30)
    (by rw [P 14 29 (by decide)]; exact z29)
    rfl hx2Llo hx2Lhi haLlo haLhi haL24
  have A38 : cAt c k 16 s 38 = xLAOf c k s := V38
  have A39 : cAt c k 16 s 39 = xLIOf c k := V39
  obtain ⟨-, V9⟩ := blkC10_spec k (cAt c k 16 s)
    (if c.tdiv ≤ qOf c k then 1 else 0) (if qOf c k = c.tdiv then 1 else 0)
    (xLIOf c k) (xLAOf c k s) (s 9)
    (by rw [P 16 18 (by decide)]; exact z18)
    (by rw [P 16 17 (by decide)]; exact z17)
    A39 A38
    (by rw [P 16 9 (by decide)]; exact z9)
    (bitLe _) (bitLe _) hxLIM hxLAM (hs.word 9)
  have A9 : cAt c k 17 s 9 = xL1Of c k s := by
    have h : cAt c k 17 s 9 =
        (if (if c.tdiv ≤ qOf c k then (1:Nat) else 0) = 0 then s 9
         else if (if qOf c k = c.tdiv then (1:Nat) else 0) = 1
           then xLIOf c k else xLAOf c k s) := V9
    rw [h, mux3', posFlip]
    rfl
  -- C11/C12: track `L`'s exponent
  obtain ⟨-, V40⟩ := blkC11_spec k (cAt c k 17 s) (s 10) (aLN c k) (gLOf c k s)
    (by rw [P 17 10 (by decide)]; exact z10)
    (by rw [P 17 29 (by decide)]; exact z29)
    (by rw [Q 17 14 37 (by decide) (by decide)]; exact A37)
    hkLNM
  have A40 : cAt c k 18 s 40 = kLNOf c k s := V40
  obtain ⟨-, V10⟩ := blkC12_spec k (cAt c k 18 s)
    (if c.tdiv ≤ qOf c k then 1 else 0) (if qOf c k = c.tdiv then 1 else 0)
    (aLN c k) (kLNOf c k s) (s 10)
    (by rw [P 18 18 (by decide)]; exact z18)
    (by rw [P 18 17 (by decide)]; exact z17)
    (by rw [P 18 29 (by decide)]; exact z29)
    A40
    (by rw [P 18 10 (by decide)]; exact z10)
    (bitLe _) (bitLe _) haLM hkLNM (hs.word 10)
  have A10 : cAt c k 19 s 10 = kL1Of c k s := by
    have h : cAt c k 19 s 10 =
        (if (if c.tdiv ≤ qOf c k then (1:Nat) else 0) = 0 then s 10
         else if (if qOf c k = c.tdiv then (1:Nat) else 0) = 1 then aLN c k
         else if kLNOf c k s ≤ KCAP then kLNOf c k s else KCAP) := V10
    rw [h, mux3', posFlip]
    rfl
  -- C13: the Padé-lower operands
  obtain ⟨-, V41⟩ := blkC13a_spec k (cAt c k 19 s) (xU1Of c k s)
    (by rw [Q 19 10 7 (by decide) (by decide)]; exact A7) hxU1
  have A41 : cAt c k 20 s 41 = uUOf c k s := V41
  obtain ⟨-, V42⟩ := blkC13b_spec k (cAt c k 20 s) (uUOf c k s) A41 hu
  have A42 : cAt c k 21 s 42 = yUOf c k s := V42
  obtain ⟨-, V43, V44⟩ := blkC13c_spec k (cAt c k 21 s) (uUOf c k s)
    (yUOf c k s) (by rw [Q 21 20 41 (by decide) (by decide)]; exact A41) A42
    rfl hu
  have A43 : cAt c k 23 s 43 = pNumUOf c k s := V43
  have A44 : cAt c k 23 s 44 = pDenUOf c k s := V44
  -- C14: the Padé-upper operands
  obtain ⟨-, V47⟩ := blkC14a_spec k (cAt c k 23 s) (xL1Of c k s)
    (by rw [Q 23 17 9 (by decide) (by decide)]; exact A9) hxL1
  have A47 : cAt c k 24 s 47 = uLOf c k s := V47
  obtain ⟨-, V49⟩ := blkC14b_spec k (cAt c k 24 s) (uLOf c k s) A47 huL
  have A49 : cAt c k 25 s 49 = pDenLOf c k s := V49
  obtain ⟨-, V48⟩ := blkC14c_spec k (cAt c k 25 s) (uLOf c k s)
    (pDenLOf c k s) (by rw [Q 25 24 47 (by decide) (by decide)]; exact A47)
    A49 rfl huL
  have A48 : cAt c k 26 s 48 = pNumLOf c k s := V48
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [cSuf c k 0 s 0 (by decide), cAt_zero]; exact z0
  · rw [cSuf c k 0 s 1 (by decide), cAt_zero]; exact z1
  · rw [cSuf c k 0 s 2 (by decide), cAt_zero]; exact z2
  · rw [cSuf c k 0 s 3 (by decide), cAt_zero]; exact z3
  · rw [cSuf c k 0 s 6 (by decide), cAt_zero]; exact z6
  · rw [cSuf c k 0 s 12 (by decide), cAt_zero]; exact z12
  · rw [cSuf c k 0 s 13 (by decide), cAt_zero]; exact z13
  · rw [cSuf c k 0 s 16 (by decide), cAt_zero]; exact z16
  · rw [cSuf c k 0 s 17 (by decide), cAt_zero]; exact z17
  · rw [cSuf c k 0 s 18 (by decide), cAt_zero]; exact z18
  · rw [cSuf c k 5 s 4 (by decide)]; exact A4
  · rw [cSuf c k 5 s 5 (by decide)]; exact A5
  · rw [cSuf c k 10 s 7 (by decide)]; exact A7
  · rw [cSuf c k 12 s 8 (by decide)]; exact A8
  · rw [cSuf c k 17 s 9 (by decide)]; exact A9
  · rw [cSuf c k 19 s 10 (by decide)]; exact A10
  · rw [cSuf c k 23 s 43 (by decide)]; exact A43
  · rw [cSuf c k 23 s 44 (by decide)]; exact A44
  · rw [cSuf c k 24 s 47 (by decide)]; exact A47
  · rw [← cAt_all]; exact A48
  · rw [cSuf c k 25 s 49 (by decide)]; exact A49

end Staged

end LeanCompCert.Ports.G1215Check

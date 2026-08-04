import LeanCompCert.Ports.G1215Check

/-!
# The staged values of the `G1215Check` round, under the invariant

Layer two of the port: names every `let` of `gRound` as a function of the
incoming register file, proves the staged register values under `Inv`, and
assembles `gRun_spec` — the body is defined at every visited index, its effect
on the carried registers is exactly `gRound`, and the invariant is preserved.
Nothing here evaluates a fold, and nothing here is a certificate.

The layer's own endgame is `gProgram_denote`: the whole program denotes the
good flag of the flat `gRound` fold *after the epilogue's two final-sum
tests*, with no fold evaluated, so the theorem costs the same at `len = 8` and
at `len = 10⁷`.
-/

namespace LeanCompCert.Ports.G1215Check

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight

set_option maxRecDepth 4000

/-! ## §5 Word-sized literals and sizing consequences -/

theorem lit0 : (0 : Nat) % M = 0 := by decide
theorem lit1 : (1 : Nat) % M = 1 := by decide
theorem lit2 : (2 : Nat) % M = 2 := by decide
theorem lit3 : (3 : Nat) % M = 3 := by decide
theorem lit4 : (4 : Nat) % M = 4 := by decide
theorem lit12 : (12 : Nat) % M = 12 := by decide
theorem lit14 : (14 : Nat) % M = 14 := by decide
theorem lit16 : (16 : Nat) % M = 16 := by decide
theorem lit17 : (17 : Nat) % M = 17 := by decide
theorem lit18 : (18 : Nat) % M = 18 := by decide
theorem lit23 : (23 : Nat) % M = 23 := by decide
theorem lit28 : (28 : Nat) % M = 28 := by decide
theorem lit39 : (39 : Nat) % M = 39 := by decide
theorem lit120 : (120 : Nat) % M = 120 := by decide
theorem lit182 : (182 : Nat) % M = 182 := by decide
theorem lit393216 : (393216 : Nat) % M = 393216 := by decide
theorem litKCAP : KCAP % M = KCAP := by decide
theorem litACAP : ACAP % M = ACAP := by decide
theorem litMB : MB % M = MB := by decide
theorem litMGUARD : MGUARD % M = MGUARD := by decide
theorem litCL : CL % M = CL := by decide
theorem litCU2 : CU2 % M = CU2 := by decide
theorem litCU : CU % M = CU := by decide
theorem litCD : CD % M = CD := by decide
theorem lit216 : (2 ^ 16 : Nat) % M = 2 ^ 16 := by decide
theorem lit232 : (2 ^ 32 : Nat) % M = 2 ^ 32 := by decide
theorem lit239 : (2 ^ 39 : Nat) % M = 2 ^ 39 := by decide
theorem lit240 : (2 ^ 40 : Nat) % M = 2 ^ 40 := by decide
theorem lit244 : (2 ^ 44 : Nat) % M = 2 ^ 44 := by decide

theorem litN39 : (549755813888 : Nat) % M = 549755813888 := by decide
theorem litN40 : (1099511627776 : Nat) % M = 1099511627776 := by decide
theorem litN44 : (17592186044416 : Nat) % M = 17592186044416 := by decide

theorem two31_lt_M : (2 : Nat) ^ 31 < M := by decide
theorem two24_lt_M : (2 : Nat) ^ 24 < M := by decide
theorem two56_lt_M : (2 : Nat) ^ 56 < M := by decide

theorem Params.Sane.RPos {c : Params} (hc : c.Sane) : 0 < c.R := by
  have := hc.tdivPos; unfold Params.R; omega

theorem Params.Sane.RLtM {c : Params} (hc : c.Sane) : c.R < M := by
  have h : c.R < 2 ^ 31 := hc.roundsSmall
  exact Nat.lt_trans h two31_lt_M

theorem Params.Sane.RModM {c : Params} (hc : c.Sane) : c.R % M = c.R :=
  Nat.mod_eq_of_lt hc.RLtM

theorem Params.Sane.tdivLtM {c : Params} (hc : c.Sane) : c.tdiv < M := by
  have h : c.R < 2 ^ 31 := hc.roundsSmall
  have : c.tdiv ≤ c.R := by unfold Params.R; omega
  exact Nat.lt_trans (by omega) two31_lt_M

theorem Params.Sane.loopLtM {c : Params} (hc : c.Sane) {k : Nat}
    (hk : k < c.len * c.R) : k < M := by
  have h1 : c.len * c.R < 2 ^ 48 := hc.loopSmall
  have h2 : (2:Nat) ^ 48 < M := by decide
  omega

theorem Params.Sane.qLt {c : Params} (hc : c.Sane) {k : Nat}
    (hk : k < c.len * c.R) : k / c.R < c.len :=
  (Nat.div_lt_iff_lt_mul hc.RPos).mpr hk

/-- The candidate at a visited index is in range. -/
theorem Params.Sane.candLt {c : Params} (hc : c.Sane) {k : Nat}
    (hk : k < c.len * c.R) : c.lo + k / c.R < c.lo + c.len := by
  have := hc.qLt hk; omega

theorem Params.Sane.candGe {c : Params} (hc : c.Sane) {k : Nat} :
    1 ≤ c.lo + k / c.R :=
  Nat.le_trans hc.loPos (Nat.le_add_right _ _)

/-! ## §6 Arithmetic helpers -/

theorem modId {a : Nat} (h : a < M) : a % M = a := Nat.mod_eq_of_lt h

/-- `a − b` computed in `u64`, for `b ≤ a < 2⁶⁴`. -/
theorem subExact (a b : Nat) (hba : b ≤ a) (ha : a < M) :
    (a + (M - b)) % M = a - b := by
  have hbM : b < M := by omega
  rw [show a + (M - b) = M + (a - b) by omega, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- `a − (a / b)·b` computed in `u64` is `a % b`. -/
theorem peelSub (a b : Nat) (hb : 0 < b) (ha : a < M) :
    (a + (M - a / b * b % M)) % M = a % b := by
  have h : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have hlt : a % b < b := Nat.mod_lt a hb
  have hc : a / b * b = b * (a / b) := Nat.mul_comm _ _
  rw [hc, Nat.mod_eq_of_lt (show b * (a / b) < M by omega),
    show a + (M - b * (a / b)) = M + a % b by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show a % b < M by omega)]

theorem bitLe (P : Prop) [Decidable P] : (if P then (1:Nat) else 0) ≤ 1 := by
  split <;> omega

theorem bitLtM (P : Prop) [Decidable P] : (if P then (1:Nat) else 0) < M := by
  have := bitLe P
  have : (2:Nat) ≤ M := by decide
  omega

theorem bitMod (P : Prop) [Decidable P] :
    (if P then (1:Nat) else 0) % M = (if P then 1 else 0) :=
  modId (bitLtM P)

theorem bit_or_le (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : x ||| y ≤ 1 := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;>
    rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl <;> decide

theorem or_mod (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) : (x ||| y) % M = x ||| y := by
  refine Nat.mod_eq_of_lt ?_
  have h1 := bit_or_le x y hx hy
  have h2 : (2:Nat) ≤ M := by decide
  omega

/-- The mantissa advance stays inside a word: the product `X·n` does. -/
theorem advX_prod_lt {n x : Nat} (hx : x < MB) (hn : n < 2 ^ 24) :
    (MB + x) * n < M := by
  have h1 : MB + x < 2 ^ 40 := by simp only [MB] at hx ⊢; omega
  have h2 : (MB + x) * n < 2 ^ 40 * 2 ^ 24 :=
    Nat.mul_lt_mul_of_lt_of_lt h1 hn
  have h3 : (2:Nat) ^ 40 * 2 ^ 24 = M := by decide
  omega

theorem advX_lt {n a x : Nat} (hx : x < MB) (hn : n < 2 ^ 24) :
    advX n a x < M := by
  unfold advX
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (advX_prod_lt hx hn)

/-- The advance is in `[2³⁹, 2⁴¹)` when the exponent is the candidate's own
`⌊log₂⌋`, so one conditional halving renormalises it. -/
theorem advX_band {n a x : Nat} (hx : x < MB) (hlo : 2 ^ a ≤ n)
    (hhi : n < 2 ^ (a + 1)) : MB ≤ advX n a x ∧ advX n a x < 2 ^ 41 := by
  constructor
  · unfold advX
    refine Nat.le_div_iff_mul_le (Nat.two_pow_pos a) |>.mpr ?_
    calc MB * 2 ^ a ≤ MB * n := Nat.mul_le_mul_left _ hlo
      _ ≤ (MB + x) * n := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · unfold advX
    refine Nat.div_lt_of_lt_mul ?_
    have h1 : MB + x < 2 ^ 40 := by simp only [MB] at hx ⊢; omega
    have h2 : (MB + x) * n < 2 ^ 40 * 2 ^ (a + 1) :=
      Nat.mul_lt_mul_of_lt_of_lt h1 hhi
    have h3 : (2:Nat) ^ 40 * 2 ^ (a + 1) = 2 ^ 41 * 2 ^ a := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    omega

/-- The renormalised advance is a `39`-bit mantissa. -/
theorem advRenorm_band {y : Nat} (hlo : MB ≤ y) (hhi : y < 2 ^ 41) :
    MB ≤ y / 2 ^ (if 2 ^ 40 ≤ y then 1 else 0) ∧
      y / 2 ^ (if 2 ^ 40 ≤ y then 1 else 0) < 2 ^ 40 := by
  by_cases hg : 2 ^ 40 ≤ y
  · rw [if_pos hg, show (2:Nat) ^ 1 = 2 from rfl]
    have hd1 : MB ≤ y / 2 :=
      (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by simp only [MB]; omega)
    have hd2 : y / 2 < 2 ^ 40 := Nat.div_lt_of_lt_mul (by omega)
    exact ⟨hd1, hd2⟩
  · rw [if_neg hg, show (2:Nat) ^ 0 = 1 from rfl, Nat.div_one]
    omega

/-! ## §7 Stage specifications

Each block's effect, from an abstract incoming state, with every `% M`
truncation discharged from hypotheses supplied by the caller.  No literal
above a few million is ever unfolded: it enters as a variable through one of
the `… % M = …` hypotheses. -/

/-- **Stage A1**: decode, per-candidate reset, round masks. -/
theorem blkA1_spec (c : Params) (k : Nat) (t : RegState) (j q : Nat)
    (h11 : t 11 = j) (h12 : t 12 = q)
    (hloM : c.lo % M = c.lo) (hnM : (c.lo + j) % M = c.lo + j)
    (hdM : (q + 2) % M = q + 2)
    (hR1M : (c.R - 1) % M = c.R - 1) (htdM : c.tdiv % M = c.tdiv)
    (h1M : t 1 % M = t 1) (h2M : t 2 % M = t 2) (h3M : t 3 % M = t 3)
    (h6M : t 6 % M = t 6) :
    (∀ i, i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 6 → i ≠ 13 → i ≠ 14 → i ≠ 15 →
      i ≠ 16 → i ≠ 17 → i ≠ 18 → run k t (blkA1 c) i = t i) ∧
    run k t (blkA1 c) 13 = c.lo + j ∧
    run k t (blkA1 c) 14 = q + 2 ∧
    run k t (blkA1 c) 15 = (if q = 0 then 1 else 0) ∧
    run k t (blkA1 c) 16 = (if q = c.R - 1 then 1 else 0) ∧
    run k t (blkA1 c) 17 = (if q = c.tdiv then 1 else 0) ∧
    run k t (blkA1 c) 18 = (if c.tdiv ≤ q then 1 else 0) ∧
    run k t (blkA1 c) 1 = (if q = 0 then c.lo + j else t 1) ∧
    run k t (blkA1 c) 2 = (if q = 0 then 1 else t 2) ∧
    run k t (blkA1 c) 3 = (if q = 0 then 1 else t 3) ∧
    run k t (blkA1 c) 6 = (if q = 0 then 0 else t 6) := by
  have hframe : ∀ i, i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 6 → i ≠ 13 → i ≠ 14 →
      i ≠ 15 → i ≠ 16 → i ≠ 17 → i ≠ 18 → run k t (blkA1 c) i = t i := by
    intro i e1 e2 e3 e6 e13 e14 e15 e16 e17 e18
    simp [run, blkA1, RegState.set, e1, e2, e3, e6, e13, e14, e15, e16, e17, e18]
  by_cases hz : q = 0
  · refine ⟨hframe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkA1, evalExpr, denoteOp, RegState.set, sel, h11, h12, hz,
        hloM, hnM, hdM, hR1M, htdM, h1M, h2M, h3M, h6M, lit0, lit1, lit2,
        ge_iff_le]
  · refine ⟨hframe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [run, blkA1, evalExpr, denoteOp, RegState.set, sel, h11, h12, hz,
        hloM, hnM, hdM, hR1M, htdM, h1M, h2M, h3M, h6M, lit0, lit1, lit2,
        ge_iff_le]

/-- **Stage A2**: `⌊log₂ n⌋` and `⌊log₂ (n+1)⌋`, with their powers. -/
theorem blkA2_spec (k : Nat) (t : RegState) (n : Nat) (h13 : t 13 = n)
    (h1n : 1 ≤ n) (h24 : n < 2 ^ 24) :
    (∀ i, i ≠ 27 → i ≠ 28 → i ≠ 29 → i ≠ 30 → run k t blkA2 i = t i) ∧
    run k t blkA2 27 = aOf n ∧
    run k t blkA2 28 = 2 ^ aOf n ∧
    run k t blkA2 29 = aOf (n + 1) ∧
    run k t blkA2 30 = 2 ^ aOf (n + 1) := by
  have h25 : n < 2 ^ 25 := by omega
  obtain ⟨ha24, hpow, hpow'⟩ := aOf_bounds h1n h25
  have hb : ∀ v : Nat, (if v ≤ n then (1:Nat) else 0) ≤ 1 := fun v => bitLe _
  have haLtM : aOf n < M := by
    have : (24:Nat) < M := by decide
    omega
  -- the indicator sum is `aOf n`
  have hsum : run k t blkA2 27 = aOf n := by
    have b2 := hb 2; have b4 := hb 4; have b8 := hb 8; have b16 := hb 16
    have b32 := hb 32; have b64 := hb 64; have b128 := hb 128
    have b256 := hb 256; have b512 := hb 512; have b1024 := hb 1024
    have b2048 := hb 2048; have b4096 := hb 4096; have b8192 := hb 8192
    have b16384 := hb 16384; have b32768 := hb 32768; have b65536 := hb 65536
    have b17 := hb 131072; have b18 := hb 262144; have b19 := hb 524288
    have b20 := hb 1048576; have b21 := hb 2097152; have b22 := hb 4194304
    have b23 := hb 8388608; have b24 := hb 16777216
    simp [run, blkA2, aLoExpr, aMdExpr, aHiExpr, geBit, evalExpr, denoteOp,
      RegState.set, ge_iff_le, h13, M]
    unfold aOf ind
    omega
  have hpowv : run k t blkA2 28 = 2 ^ aOf n := by
    have h : run k t blkA2 28 = (1 <<< (run k t blkA2 27)) % M := by
      simp [run, blkA2, RegState.set, evalExpr, denoteOp, lit1]
    rw [h, hsum, Nat.shiftLeft_eq, Nat.one_mul]
    refine Nat.mod_eq_of_lt ?_
    have h1 : (2:Nat) ^ aOf n ≤ 2 ^ 24 := Nat.pow_le_pow_right (by omega) ha24
    have h2 : (2:Nat) ^ 24 < M := two24_lt_M
    omega
  -- `aOf (n+1)` is `aOf n` plus one comparison
  have hstep : aOf (n + 1) = aOf n + (if 2 * 2 ^ aOf n ≤ n + 1 then 1 else 0) := by
    have h25' : n + 1 < 2 ^ 25 := by omega
    have hlog : aOf n = Nat.log2 n := aOf_eq_log2 h1n h25
    have hlog' : aOf (n + 1) = Nat.log2 (n + 1) := aOf_eq_log2 (by omega) h25'
    have hne : n ≠ 0 := by omega
    have hne' : n + 1 ≠ 0 := by omega
    by_cases hb2 : 2 * 2 ^ aOf n ≤ n + 1
    · rw [if_pos hb2, hlog, hlog']
      have hge : (2:Nat) ^ (Nat.log2 n + 1) ≤ n + 1 := by
        rw [Nat.pow_succ, Nat.mul_comm]
        rw [hlog] at hb2
        omega
      have h1' : Nat.log2 n + 1 ≤ Nat.log2 (n + 1) := (Nat.le_log2 hne').mpr hge
      have h2' : Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
        refine Nat.le_of_lt_succ ((Nat.log2_lt hne').mpr ?_)
        have := hpow'
        rw [hlog] at this
        have hx : (2:Nat) ^ (Nat.log2 n + 1 + 1) = 2 * 2 ^ (Nat.log2 n + 1) := by
          rw [Nat.pow_succ]; omega
        omega
      omega
    · rw [if_neg hb2, hlog, hlog', Nat.add_zero]
      have hlt : n + 1 < 2 ^ (Nat.log2 n + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
        rw [hlog] at hb2
        omega
      have h2' : Nat.log2 (n + 1) ≤ Nat.log2 n :=
        Nat.le_of_lt_succ ((Nat.log2_lt hne').mpr hlt)
      have h1' : Nat.log2 n ≤ Nat.log2 (n + 1) := by
        refine (Nat.le_log2 hne').mpr ?_
        have := hpow
        rw [hlog] at this
        omega
      omega
  have haL : run k t blkA2 29 = aOf (n + 1) := by
    have h : run k t blkA2 29 =
        (run k t blkA2 27 +
          (if 2 % M * (run k t blkA2 28) % M ≤ (t 13 + 1 % M) % M
            then 1 else 0)) % M := by
      simp [run, blkA2, RegState.set, evalExpr, denoteOp, ge_iff_le]
    rw [h, hsum, hpowv, h13, lit1, lit2, modId (show n + 1 < M by
      have : (2:Nat) ^ 24 < M := two24_lt_M; omega)]
    have hp : 2 * 2 ^ aOf n < M := by
      have h1 : (2:Nat) ^ aOf n ≤ 2 ^ 24 := Nat.pow_le_pow_right (by omega) ha24
      have h2 : (2:Nat) ^ 25 < M := by decide
      have : (2:Nat) * 2 ^ 24 = 2 ^ 25 := by decide
      omega
    rw [modId hp, ← hstep]
    refine modId ?_
    have h25' : n + 1 < 2 ^ 25 := by omega
    obtain ⟨ha24', _, _⟩ := aOf_bounds (show 1 ≤ n + 1 by omega) h25'
    have : (25:Nat) < M := by decide
    omega
  refine ⟨?_, hsum, hpowv, haL, ?_⟩
  · intro i h27 h28 h29 h30
    simp [run, blkA2, RegState.set, h27, h28, h29, h30]
  · have h : run k t blkA2 30 = (1 <<< (run k t blkA2 29)) % M := by
      simp [run, blkA2, RegState.set, evalExpr, denoteOp, lit1]
    rw [h, haL, Nat.shiftLeft_eq, Nat.one_mul]
    refine Nat.mod_eq_of_lt ?_
    have h25' : n + 1 < 2 ^ 25 := by omega
    obtain ⟨ha24', _, _⟩ := aOf_bounds (show 1 ≤ n + 1 by omega) h25'
    have h1 : (2:Nat) ^ aOf (n + 1) ≤ 2 ^ 24 :=
      Nat.pow_le_pow_right (by omega) ha24'
    have h2 : (2:Nat) ^ 24 < M := two24_lt_M
    omega

/-- **Stage B1**: the divisibility flag and the squarefree update. -/
theorem blkB1_spec (k : Nat) (t : RegState) (m0 sq0 d : Nat)
    (h1 : t 1 = m0) (h3 : t 3 = sq0) (h14 : t 14 = d)
    (h19 : t 19 = m0 / d) (h20 : t 20 = m0 / d / d)
    (hd0 : 0 < d) (hm0M : m0 < M) (hsq0 : sq0 ≤ 1) :
    (∀ i, i ≠ 3 → i ≠ 21 → run k t blkB1 i = t i) ∧
    run k t blkB1 21 = (if m0 % d = 0 then 1 else 0) ∧
    run k t blkB1 3 = (if m0 % d = 0 ∧ m0 / d % d = 0 then 0 else sq0) := by
  have hdivM : m0 / d < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M
  have e1 : (m0 + (M - m0 / d * d % M)) % M = m0 % d := peelSub m0 d hd0 hm0M
  have e2 : (m0 / d + (M - m0 / d / d * d % M)) % M = m0 / d % d :=
    peelSub (m0 / d) d hd0 hdivM
  have hframe : ∀ i, i ≠ 3 → i ≠ 21 → run k t blkB1 i = t i := by
    intro i e3 e21
    simp [run, blkB1, RegState.set, e3, e21]
  have h21 : run k t blkB1 21 = (if m0 % d = 0 then 1 else 0) := by
    simp [run, blkB1, evalExpr, denoteOp, RegState.set, h1, h14, h19, h20,
      lit0, e1]
  refine ⟨hframe, h21, ?_⟩
  have hsq0M : sq0 < M := by
    have h2M : (2:Nat) ≤ M := by decide
    omega
  by_cases ha : m0 % d = 0
  · by_cases hb : m0 / d % d = 0
    · rw [if_pos (And.intro ha hb)]
      simp [run, blkB1, evalExpr, denoteOp, RegState.set, h1, h3, h14, h19,
        h20, lit0, lit1, e1, e2, ha, hb]
    · rw [if_neg (show ¬ (m0 % d = 0 ∧ m0 / d % d = 0) from fun hc => hb hc.2)]
      simp [run, blkB1, evalExpr, denoteOp, RegState.set, h1, h3, h14, h19,
        h20, lit0, lit1, e1, e2, ha, hb, modId hsq0M]
  · rw [if_neg (show ¬ (m0 % d = 0 ∧ m0 / d % d = 0) from fun hc => ha hc.1)]
    simp [run, blkB1, evalExpr, denoteOp, RegState.set, h1, h3, h14, h19,
      h20, lit0, lit1, e1, e2, ha, modId hsq0M]

/-- **Stage B2**: the totient product and cofactor updates. -/
theorem blkB2_spec (k : Nat) (t : RegState) (m0 phi0 q d : Nat)
    (h1 : t 1 = m0) (h2 : t 2 = phi0) (h12 : t 12 = q)
    (h19 : t 19 = m0 / d) (h21 : t 21 = (if m0 % d = 0 then 1 else 0))
    (hdq : d = q + 2) (hq1M : (q + 1) % M = q + 1)
    (hprodM : (phi0 * (q + 1)) % M = phi0 * (q + 1))
    (hm0M : m0 < M) (hphi0M : phi0 < M) :
    (∀ i, i ≠ 1 → i ≠ 2 → run k t blkB2 i = t i) ∧
    run k t blkB2 2 = (if m0 % d = 0 then phi0 * (d - 1) else phi0) ∧
    run k t blkB2 1 = (if m0 % d = 0 then m0 / d else m0) := by
  have hdivM : m0 / d < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm0M
  have hd1 : d - 1 = q + 1 := by omega
  have hframe : ∀ i, i ≠ 1 → i ≠ 2 → run k t blkB2 i = t i := by
    intro i e1 e2
    simp [run, blkB2, RegState.set, e1, e2]
  refine ⟨hframe, ?_, ?_⟩
  · rw [hd1]
    by_cases ha : m0 % d = 0 <;>
      simp [run, blkB2, evalExpr, denoteOp, RegState.set, sel, h1, h2, h12,
        h19, h21, ha, lit0, lit1, hq1M, hprodM, modId hm0M, modId hphi0M,
        modId hdivM]
  · by_cases ha : m0 % d = 0 <;>
      simp [run, blkB2, evalExpr, denoteOp, RegState.set, sel, h1, h2, h12,
        h19, h21, ha, lit0, lit1, hq1M, hprodM, modId hm0M, modId hphi0M,
        modId hdivM]

/-- **Stage B3**: the totient decode. -/
theorem blkB3_spec (k : Nat) (t : RegState) (m1 phi1 : Nat)
    (h1 : t 1 = m1) (h2 : t 2 = phi1) (hm1M : m1 < M) (hphi1M : phi1 < M)
    (hprodM : (phi1 * (m1 - 1)) % M = phi1 * (m1 - 1)) (hm1 : 0 < m1) :
    (∀ i, i ≠ 22 → run k t blkB3 i = t i) ∧
    run k t blkB3 22 = (if 1 < m1 then phi1 * (m1 - 1) else phi1) := by
  have hframe : ∀ i, i ≠ 22 → run k t blkB3 i = t i := by
    intro i e22
    simp [run, blkB3, RegState.set, e22]
  refine ⟨hframe, ?_⟩
  have hsub : (m1 + (M - 1)) % M = m1 - 1 := subExact m1 1 hm1 hm1M
  by_cases hgt : 1 < m1 <;>
    simp [run, blkB3, evalExpr, denoteOp, RegState.set, sel, h1, h2, hgt,
      lit1, hsub, hprodM, modId hphi1M]

/-- **Stage C1a**: the exactness bit of `2⁴⁴/φ`. -/
theorem blkC1a_spec (k : Nat) (t : RegState) (phiF : Nat)
    (h22 : t 22 = phiF) (h23 : t 23 = 2 ^ 44 / phiF) (hphi : 0 < phiF) :
    (∀ i, i ≠ 24 → run k t blkC1a i = t i) ∧
    run k t blkC1a 24 = (if 2 ^ 44 % phiF = 0 then 1 else 0) := by
  have e1 : (2 ^ 44 + (M - 2 ^ 44 / phiF * phiF % M)) % M = 2 ^ 44 % phiF :=
    peelSub (2 ^ 44) phiF hphi (by decide)
  refine ⟨?_, ?_⟩
  · intro i e24
    simp [run, blkC1a, RegState.set, e24]
  · simp [run, blkC1a, evalExpr, denoteOp, RegState.set, h22, h23, lit0,
      lit244, e1]

/-- **Stage C1b**: the ceiling term and the floor term. -/
theorem blkC1b_spec (k : Nat) (t : RegState) (sq1 tq ex : Nat)
    (h3 : t 3 = sq1) (h23 : t 23 = tq)
    (h24 : t 24 = (if ex = 0 then 1 else 0))
    (hsq : sq1 ≤ 1) (htqM : tq + 1 < M) :
    (∀ i, i ≠ 25 → i ≠ 26 → run k t blkC1b i = t i) ∧
    run k t blkC1b 25 = sq1 * (tq + (if ex = 0 then 0 else 1)) ∧
    run k t blkC1b 26 = sq1 * tq := by
  have hmul1 : sq1 * (tq + 1) < M := by
    rcases (show sq1 = 0 ∨ sq1 = 1 by omega) with rfl | rfl <;> omega
  have hmul0 : sq1 * tq < M := by
    rcases (show sq1 = 0 ∨ sq1 = 1 by omega) with rfl | rfl <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro i e25 e26
    simp [run, blkC1b, RegState.set, e25, e26]
  · by_cases hx : ex = 0
    · simp [run, blkC1b, evalExpr, denoteOp, RegState.set, h3, h23, h24, hx,
        lit1, modId hmul0]
    · have h1 : ((0:Nat) ^^^ 1) = 1 := by decide
      simp [run, blkC1b, evalExpr, denoteOp, RegState.set, h3, h23, h24, hx,
        lit1, modId hmul1]
  · simp [run, blkC1b, evalExpr, denoteOp, RegState.set, h3, h23, modId hmul0]

/-- **Stage C2**: the two accumulator steps. -/
theorem blkC2_spec (k : Nat) (t : RegState) (accU accL e0 tU tL : Nat)
    (h4 : t 4 = accU) (h5 : t 5 = accL) (h17 : t 17 = e0)
    (h25 : t 25 = tU) (h26 : t 26 = tL) (he0 : e0 ≤ 1)
    (htUM : tU < M) (htLM : tL < M) :
    (∀ i, i ≠ 4 → i ≠ 5 → run k t blkC2 i = t i) ∧
    run k t blkC2 4 = (accU + (if e0 = 1 then tU else 0)) % M ∧
    run k t blkC2 5 = (accL + (if e0 = 1 then tL else 0)) % M := by
  refine ⟨?_, ?_, ?_⟩
  · intro i e4 e5
    simp [run, blkC2, RegState.set, e4, e5]
  · rcases (show e0 = 0 ∨ e0 = 1 by omega) with rfl | rfl <;>
      simp [run, blkC2, evalExpr, denoteOp, RegState.set, h4, h17, h25,
        modId htUM]
  · rcases (show e0 = 0 ∨ e0 = 1 by omega) with rfl | rfl <;>
      simp [run, blkC2, evalExpr, denoteOp, RegState.set, h5, h17, h26,
        modId htLM]

/-! ### The mantissa blocks

Both tracks have the same six-block shape; only the registers and the
candidate differ.  The two `sub` instructions are exact under the band
(`advRenorm_band` and `2^a ≤ n`), so no wrapped difference is ever formed. -/

/-! ### HANDOFF — the six mantissa-block specifications are NOT proved

`blkC3a`/`blkC3b`/`blkC4` (track `U`) and `blkC8a`/`blkC8b`/`blkC9`
(track `L`) are the only blocks whose value lemmas this file does not carry.
Their statements are written out below as comments, with the arithmetic they
need already proved above (`advX_prod_lt`, `advX_band`, `advRenorm_band`,
`subExact`, `modId`).  What defeated the last pass was purely `simp`
normalisation, not mathematics: `simp` rewrites `2 ^ 39` / `2 ^ 40` to their
numerals before the `… % M = …` facts can fire, so the mod-elimination
hypotheses have to be stated in numeral form *and* introduced by `rw` rather
than as `simp` lemmas.  `litN39` / `litN40` above are those numeral forms.

```text
theorem blkC3a_spec (k) (t) (xU n aU)
    (h7 : t 7 = xU) (h13 : t 13 = n) (h27 : t 27 = aU)
    (hx : xU < MB) (hn : n < 2 ^ 24) :
    (∀ i, i ≠ 31 → run k t blkC3a i = t i) ∧
    run k t blkC3a 31 = advX n aU xU

theorem blkC3b_spec (k) (t) (x2) (h31 : t 31 = x2) :
    (∀ i, i ≠ 32 → run k t blkC3b i = t i) ∧
    run k t blkC3b 32 = (if 2 ^ 40 ≤ x2 then 1 else 0)

theorem blkC4_spec (k) (t) (x2 g n aU)
    (h31 : t 31 = x2) (h32 : t 32 = g) (h13 : t 13 = n)
    (h28 : t 28 = 2 ^ aU) (h27 : t 27 = aU)
    (hg : g = (if 2 ^ 40 ≤ x2 then 1 else 0))
    (hlo : MB ≤ x2) (hhi : x2 < 2 ^ 41) (hna : 2 ^ aU ≤ n)
    (hn1 : n < 2 ^ (aU + 1)) (haU : aU ≤ 24) :
    (∀ i, i ≠ 33 → i ≠ 34 → run k t blkC4 i = t i) ∧
    run k t blkC4 33 = x2 / 2 ^ g - MB ∧
    run k t blkC4 34 = (n - 2 ^ aU) * 2 ^ (39 - aU)
```

and the same three for track `L` at registers `36`/`37`/`38`/`39`, candidate
`n + 1` and exponent `aL`.  After them the round assembly (`gRun_spec`,
`gBody_defined`, `gStep_spec`, `gProgram_denote`, with the epilogue's two
final-sum tests threaded through `denote_eq_foldl_mem`'s `fin`) and the
per-candidate re-blocking of `Ports/G1215CheckSpec.lean` remain; both are
transcriptions of `Ports/GFoldCheckRun.lean` §11–§13 and
`Ports/GFoldCheckSpec.lean`, which this port's block structure was chosen to
mirror. -/

/-- **Stage C5**: track `U`'s mantissa select. -/
theorem blkC5_spec (k : Nat) (t : RegState) (ep e0 ini adv old : Nat)
    (h18 : t 18 = ep) (h17 : t 17 = e0) (h34 : t 34 = ini) (h33 : t 33 = adv)
    (h7 : t 7 = old) (hep : ep ≤ 1) (he0 : e0 ≤ 1)
    (hiniM : ini < M) (hadvM : adv < M) (holdM : old < M) :
    (∀ i, i ≠ 7 → run k t blkC5 i = t i) ∧
    run k t blkC5 7 =
      (if ep = 0 then old else if e0 = 1 then ini else adv) := by
  refine ⟨?_, ?_⟩
  · intro i e7
    simp [run, blkC5, RegState.set, e7]
  · rcases (show ep = 0 ∨ ep = 1 by omega) with rfl | rfl <;>
      rcases (show e0 = 0 ∨ e0 = 1 by omega) with rfl | rfl <;>
      simp [run, blkC5, evalExpr, denoteOp, RegState.set, sel, h18, h17, h34,
        h33, h7, lit1, modId hiniM, modId hadvM, modId holdM]

/-- **Stage C6**: track `U`'s unclamped exponent. -/
theorem blkC6_spec (k : Nat) (t : RegState) (kU aU g : Nat)
    (h8 : t 8 = kU) (h27 : t 27 = aU) (h32 : t 32 = g)
    (hsum : kU + aU + g < M) :
    (∀ i, i ≠ 35 → run k t blkC6 i = t i) ∧
    run k t blkC6 35 = kU + aU + g := by
  refine ⟨?_, ?_⟩
  · intro i e35
    simp [run, blkC6, RegState.set, e35]
  · simp [run, blkC6, evalExpr, denoteOp, RegState.set, h8, h27, h32,
      modId (show kU + aU < M by omega), modId hsum]

/-- **Stage C7**: track `U`'s exponent select. -/
theorem blkC7_spec (k : Nat) (t : RegState) (ep e0 aU kN kOld : Nat)
    (h18 : t 18 = ep) (h17 : t 17 = e0) (h27 : t 27 = aU) (h35 : t 35 = kN)
    (h8 : t 8 = kOld) (hep : ep ≤ 1) (he0 : e0 ≤ 1)
    (haM : aU < M) (hkNM : kN < M) (hkOldM : kOld < M) :
    (∀ i, i ≠ 8 → run k t blkC7 i = t i) ∧
    run k t blkC7 8 =
      (if ep = 0 then kOld
       else if e0 = 1 then aU else if kN ≤ KCAP then kN else KCAP) := by
  refine ⟨?_, ?_⟩
  · intro i e8
    simp [run, blkC7, RegState.set, e8]
  · rcases (show ep = 0 ∨ ep = 1 by omega) with rfl | rfl <;>
      rcases (show e0 = 0 ∨ e0 = 1 by omega) with rfl | rfl <;>
      by_cases hk : kN ≤ KCAP <;>
      simp [run, blkC7, evalExpr, denoteOp, RegState.set, sel, h18, h17, h27,
        h35, h8, hk, lit1, litKCAP, modId haM, modId hkNM, modId hkOldM]

/-- **Stage C10**: track `L`'s mantissa select. -/
theorem blkC10_spec (k : Nat) (t : RegState) (ep e0 ini adv old : Nat)
    (h18 : t 18 = ep) (h17 : t 17 = e0) (h39 : t 39 = ini) (h38 : t 38 = adv)
    (h9 : t 9 = old) (hep : ep ≤ 1) (he0 : e0 ≤ 1)
    (hiniM : ini < M) (hadvM : adv < M) (holdM : old < M) :
    (∀ i, i ≠ 9 → run k t blkC10 i = t i) ∧
    run k t blkC10 9 =
      (if ep = 0 then old else if e0 = 1 then ini else adv) := by
  refine ⟨?_, ?_⟩
  · intro i e9
    simp [run, blkC10, RegState.set, e9]
  · rcases (show ep = 0 ∨ ep = 1 by omega) with rfl | rfl <;>
      rcases (show e0 = 0 ∨ e0 = 1 by omega) with rfl | rfl <;>
      simp [run, blkC10, evalExpr, denoteOp, RegState.set, sel, h18, h17, h39,
        h38, h9, lit1, modId hiniM, modId hadvM, modId holdM]

/-- **Stage C11**: track `L`'s unclamped exponent. -/
theorem blkC11_spec (k : Nat) (t : RegState) (kL aL g : Nat)
    (h10 : t 10 = kL) (h29 : t 29 = aL) (h37 : t 37 = g)
    (hsum : kL + aL + g < M) :
    (∀ i, i ≠ 40 → run k t blkC11 i = t i) ∧
    run k t blkC11 40 = kL + aL + g := by
  refine ⟨?_, ?_⟩
  · intro i e40
    simp [run, blkC11, RegState.set, e40]
  · simp [run, blkC11, evalExpr, denoteOp, RegState.set, h10, h29, h37,
      modId (show kL + aL < M by omega), modId hsum]

/-- **Stage C12**: track `L`'s exponent select. -/
theorem blkC12_spec (k : Nat) (t : RegState) (ep e0 aL kN kOld : Nat)
    (h18 : t 18 = ep) (h17 : t 17 = e0) (h29 : t 29 = aL) (h40 : t 40 = kN)
    (h10 : t 10 = kOld) (hep : ep ≤ 1) (he0 : e0 ≤ 1)
    (haM : aL < M) (hkNM : kN < M) (hkOldM : kOld < M) :
    (∀ i, i ≠ 10 → run k t blkC12 i = t i) ∧
    run k t blkC12 10 =
      (if ep = 0 then kOld
       else if e0 = 1 then aL else if kN ≤ KCAP then kN else KCAP) := by
  refine ⟨?_, ?_⟩
  · intro i e10
    simp [run, blkC12, RegState.set, e10]
  · rcases (show ep = 0 ∨ ep = 1 by omega) with rfl | rfl <;>
      rcases (show e0 = 0 ∨ e0 = 1 by omega) with rfl | rfl <;>
      by_cases hk : kN ≤ KCAP <;>
      simp [run, blkC12, evalExpr, denoteOp, RegState.set, sel, h18, h17, h29,
        h40, h10, hk, lit1, litKCAP, modId haM, modId hkNM, modId hkOldM]

end LeanCompCert.Ports.G1215Check

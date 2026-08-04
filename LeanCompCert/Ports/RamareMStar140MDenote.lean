import LeanCompCert.Ports.RamareMStar140MRound
import LeanCompCert.Ports.BlockedFold

/-!
# `MSEncoding`, discharged: the `m★` program denotes `msRef`

`Ports/RamareMStar140MRound.lean` says what **one flat round** does.  This
module re-blocks `len · B` of them into `len` candidates
(`Ports/BlockedFold.lean`), identifies one block with `msStep`, runs the
initialization block, and assembles the three through
`ArrayFoldBridge.AProgram.denote_eq_obs_foldl_mem`.

★ The observation carries the **array**, which is what distinguishes this port
from `Ports/RamareWM217.lean` (whose array is read-only).  The one fact that
makes the re-blocking work is `msRound_arr_indep`: a round never reads the
cell its own candidate is about to write, so the value stored there by earlier
rounds of the same block — the *previous* candidate's packed cell — is invisible.
That is exactly why the body can afford an unconditional `store`.
-/

namespace LeanCompCert.Ports.RamareMStar140M

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.BlockedFold
open LeanCompCert.Verified.InstrBlock
  (srun sval sdest SDefined SAllDefined NoDivI srun_append SAllDefined_append)

/-! ## The candidate-level view of a round state -/

/-- A round state, forgetting the three registers a candidate consumes. -/
def toSt (st : RSt) : St :=
  { bad := st.bad, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs
  , mx := st.mx, cell := st.cell, arr := st.arr }

/-- What holds at every block boundary: every carried quantity is a word, and
the log slot is in the table. -/
def BInv (c : Cfg) (st : RSt) : Prop :=
  st.bad < M ∧ st.lb < M ∧ st.lam < M ∧ st.idx < c.tab ∧ st.bs < M ∧
    st.mx < M ∧ st.cell < M ∧ st.acc < M ∧ st.sc < M ∧ st.muQ < M ∧
    (∀ i, st.arr i < M) ∧ (st.sc = 0 ∨ 2 ≤ st.sc)

/-! ## Small arithmetic helpers

`omega`'s cost is the size of the context it scans, so every arithmetic step
below is a top-level lemma with two or three hypotheses and no `2⁴⁸`-scale
numeral in sight.
-/

private theorem MS_one_zero : MS 1 0 = 1 := by
  show (1 + (M - 0)) % M = 1
  rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt one_lt_M]

private theorem MS_one_one : MS 1 1 = 0 := by
  show (1 + (M - 1)) % M = 0
  have h : 1 + (M - 1) = M := by have := one_lt_M; omega
  rw [h, Nat.mod_self]

private theorem MA_zero_zero : MA 0 0 = 0 := MA_zero_right (by decide)

/-- A flag is `< M`, so `MMul _ 1` and `MMul 1 _` collapse on it. -/
private theorem MMul_bit_one (p : Prop) [Decidable p] : MMul (bitOf p) 1 = bitOf p :=
  MMul_one_right (bitOf_lt p)

private theorem bitOf_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    bitOf p = bitOf q := by
  unfold bitOf
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun t => hp (h.mpr t))]

/-- The flat index decodes to `(q, r)`; `Ports/RamareWM217.lean`'s `idx_decode`. -/
private theorem idx_decode (B q r : Nat) (hB : 0 < B) (hr : r < B) :
    (q * B + r) % B = r ∧ (q * B + r) / B = q := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm q B, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  · rw [Nat.mul_comm q B, Nat.add_comm (B * q) r, Nat.add_mul_div_left r q hB,
      Nat.div_eq_of_lt hr, Nat.zero_add]

/-- The three round kinds are exhaustive. -/
private theorem round_trichotomy {B r : Nat} (hB : 3 ≤ B) (hr : r < B) :
    r < B - 2 ∨ r = B - 2 ∨ r = B - 1 := by omega

private theorem sq_small {B r : Nat} (hB : B + 1 < 2 ^ 20) (hr : r < B) :
    (r + 2) * (r + 2) < M := by
  have h2 : (r + 2) * (r + 2) ≤ 2 ^ 20 * 2 ^ 20 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (2:Nat) ^ 20 * 2 ^ 20 < M := by decide
  omega

/-! ## The store is invisible inside its own block -/

/-- The load index of one flat round, zeta-reduced out of `msRound`. -/
private def msIdx (c : Cfg) (k : Nat) (st : RSt) : Nat :=
  semI (bitOf (k % c.B < c.B - 2))
    ((c.n0 + k / c.B) / MMul (k % c.B + 2) (k % c.B + 2))
    (bitOf (k % c.B = c.B - 2))
    (semQ (semScanS (MMul st.sc (bitOf (k % c.B ≠ 0)))
        (MMul (k % c.B + 2) (k % c.B + 2)) (c.n0 + k / c.B) (k % c.B + 2)
        (bitOf (k % c.B < c.B - 2))) (c.n0 + k / c.B))
    (bitOf (k % c.B = c.B - 1)) (c.limit + 1) st.idx

/--
One round's *scalar* result, as a function of the value it loads.  The array
field is deliberately constant: what a round writes is recoverable from its
`cell`, so this function does not mention `st.arr` at all — which is exactly
what makes the two "same scalar fields" rewrites below `rfl`.
-/
private def msRoundG (c : Cfg) (k : Nat) (st : RSt) (v : Nat)
    (g : Nat → Nat → Nat) : RSt :=
  let r := k % c.B
  let n := c.n0 + k / c.B
  let d := r + 2
  let sq := MMul d d
  let w := bitOf (r < c.B - 2)
  let qg := bitOf (r = c.B - 2)
  let cc := bitOf (r = c.B - 1)
  let z := bitOf (r ≠ 0)
  let S0 := MMul st.sc z
  let acc0 := MMul st.acc z
  let S1 := semScanS S0 sq n d w
  let p := semP S1 n
  let qn := semQ S1 n
  let qq := n / sq
  let mu1 := semMu1 v
  let ab := semAbs v
  let acc1 := semAcc acc0 ab qq sq w
  let muQ1 := semMuQ qg st.muQ mu1
  let mun := semMun qn p muQ1
  let lb1 := semLb st.lb mun cc n
  let absN := semAbsN lb1
  let star := semStar acc1 absN n
  let mx1 := semMx st.mx star
  let cv := semCv n star st.mx
  let fire := semFire n c.limit st.bs
  let lam1 := semLam st.lam c.handoff n cc
  let lu := semLU n c.handoff v lam1
  let ok := semOk (MMul 5 cv) lu
  let cell1 := semCell mun absN cc st.cell
  { bad := semBadC (semBadW (semBadRow st.bad ok fire cc) acc1 ab c.capS c.capL w)
      star absN lam1 c.capS c.capL c.capLog cc
  , lb := lb1
  , lam := lam1
  , idx := semIdx st.idx cc fire c.tab
  , bs := semBs n fire st.bs cc
  , mx := semMax fire mx1 cc st.mx
  , cell := cell1
  , acc := acc1
  , sc := S1
  , muQ := muQ1
  , arr := g cell1 }

/-- `msRound` is `msRoundG` at the loaded value, with the store re-attached.
Both sides are one zeta-reduction apart — no projection of a `let`-chain is
ever forced, which is what keeps this `rfl` inside the heartbeat budget. -/
private theorem msRound_eq_G (c : Cfg) (k : Nat) (st : RSt) :
    msRound c k st = msRoundG c k st (st.arr (msIdx c k st))
      (fun cl j => if j = c.n0 + k / c.B then cl else st.arr j) := rfl

/--
**No round reads the cell its own candidate is about to write.**

Work round: `⌊n/d²⌋ ≤ n/4`.  Möbius round: `n/p` with `p ≥ 2` — which is
where the scan invariant `st.sc = 0 ∨ 2 ≤ st.sc` is load-bearing, together
with `st.sc < M`, because the round consumes `MMul st.sc z`, not `st.sc`.
Commit round: a log cell `> limit ≥ n`.
-/
private theorem msIdx_ne (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (st : RSt) (hidx : st.idx < c.tab)
    (hsc : st.sc = 0 ∨ 2 ≤ st.sc) (hscM : st.sc < M) :
    msIdx c k st ≠ c.n0 + k / c.B := by
  obtain ⟨hkM, hkdiv, hrB, hnlim⟩ := ok_idx hok hk
  have hB3 : 3 ≤ c.B := ok_B3 hok
  have hn2 : 2 ≤ c.n0 + k / c.B :=
    Nat.le_trans (ok_n0 hok) (Nat.le_add_right _ _)
  have hnM : c.n0 + k / c.B < M := Nat.lt_of_le_of_lt hnlim (ok_limM hok)
  have hsqv : MMul (k % c.B + 2) (k % c.B + 2) = (k % c.B + 2) * (k % c.B + 2) :=
    Nat.mod_eq_of_lt (sq_small (ok_Blt hok) hrB)
  have hqqM : (c.n0 + k / c.B) / MMul (k % c.B + 2) (k % c.B + 2) < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnM
  rcases round_trichotomy hB3 hrB with hcase | hcase | hcase
  · -- work round
    have hw : bitOf (k % c.B < c.B - 2) = 1 := bitOf_pos hcase
    have hqg : bitOf (k % c.B = c.B - 2) = 0 := bitOf_neg (by omega)
    have hcc : bitOf (k % c.B = c.B - 1) = 0 := bitOf_neg (by omega)
    unfold msIdx semI
    rw [hw, hqg, hcc, MMul_zero_left, MMul_zero_left, MMul_one_left hqqM,
      MA_zero_right hqqM, MA_zero_right hqqM, hsqv]
    have h1 : 1 < (k % c.B + 2) * (k % c.B + 2) := by
      have : 2 ≤ k % c.B + 2 := by omega
      exact Nat.lt_of_lt_of_le (by omega) (Nat.mul_le_mul this this)
    exact Nat.ne_of_lt (Nat.div_lt_self (by omega) h1)
  · -- Möbius round
    have hw : bitOf (k % c.B < c.B - 2) = 0 := bitOf_neg (by omega)
    have hqg : bitOf (k % c.B = c.B - 2) = 1 := bitOf_pos hcase
    have hcc : bitOf (k % c.B = c.B - 1) = 0 := bitOf_neg (by omega)
    have hz : bitOf (k % c.B ≠ 0) = 1 := bitOf_pos (by omega)
    have hS1 : semScanS (MMul st.sc (bitOf (k % c.B ≠ 0)))
        (MMul (k % c.B + 2) (k % c.B + 2)) (c.n0 + k / c.B) (k % c.B + 2)
        (bitOf (k % c.B < c.B - 2)) = st.sc := by
      rw [hw]
      unfold semScanS semScanG
      simp only [MMul_zero_right]
      rw [MS_one_zero, MMul_zero_left, hz, MMul_one_right hscM,
        MMul_one_left hscM, MA_zero_right hscM]
    have hqnM : semQ st.sc (c.n0 + k / c.B) < M := by
      unfold semQ
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnM
    unfold msIdx semI
    rw [hS1, hw, hqg, hcc, MMul_zero_left, MMul_zero_left, MMul_one_left hqnM,
      MA_zero_left hqnM, MA_zero_right hqnM]
    unfold semQ
    rw [semP_eq hscM hnM]
    rcases hsc with h0 | h2
    · rw [h0, if_pos rfl, Nat.div_self (by omega)]
      omega
    · rw [if_neg (by omega)]
      exact Nat.ne_of_lt (Nat.div_lt_self (by omega) (by omega))
  · -- commit round
    have hw : bitOf (k % c.B < c.B - 2) = 0 := bitOf_neg (by omega)
    have hqg : bitOf (k % c.B = c.B - 2) = 0 := bitOf_neg (by omega)
    have hcc : bitOf (k % c.B = c.B - 1) = 1 := bitOf_pos hcase
    have hlimM : c.limit + 1 + st.idx < M := by
      have h1 := ok_lim32 hok
      have h2 := ok_tab hok
      have h3 : (2:Nat) ^ 32 + 1 + 2 ^ 10 < M := by decide
      omega
    have hXv : MA (c.limit + 1) st.idx = c.limit + 1 + st.idx :=
      Nat.mod_eq_of_lt hlimM
    unfold msIdx semI
    rw [hw, hqg, hcc, MMul_zero_left, MMul_zero_left, MA_zero_zero, hXv,
      MMul_one_left hlimM, MA_zero_left hlimM]
    omega

/--
**A round does not see the cell its own candidate is about to write.**

Every read index is `⌊n/w²⌋ ≤ n/4`, or `q = n/p ≤ n/2`, or a log cell above
`limit` — never `n` itself.  So overwriting cell `n` with anything at all
leaves the round unchanged, which is what lets the block's earlier rounds
store the *previous* candidate's packed cell there without being observed.
-/
theorem msRound_arr_indep (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (st : RSt) (hidx : st.idx < c.tab)
    (hsc : st.sc = 0 ∨ 2 ≤ st.sc) (hscM : st.sc < M) (v : Nat) :
    msRound c k { st with arr := fun j => if j = c.n0 + k / c.B then v else st.arr j }
      = msRound c k st := by
  have hne : msIdx c k st ≠ c.n0 + k / c.B := msIdx_ne c hok k hk st hidx hsc hscM
  have hL : msRound c k
        { st with arr := fun j => if j = c.n0 + k / c.B then v else st.arr j } =
      msRoundG c k st
        (if msIdx c k st = c.n0 + k / c.B then v else st.arr (msIdx c k st))
        (fun cl j => if j = c.n0 + k / c.B then cl
          else (if j = c.n0 + k / c.B then v else st.arr j)) := rfl
  rw [if_neg hne] at hL
  rw [hL, msRound_eq_G]
  congr 1
  funext cl j
  split <;> rfl

/-! ### The fields of one round

Stated against a *variable* loaded value and a *variable* store, so that each
`rfl` is a whnf of a moderate term rather than of one with `msIdx` inlined at
three sites.
-/

private theorem bitOf_zero_or_one (p : Prop) [Decidable p] :
    bitOf p = 0 ∨ bitOf p = 1 := by
  unfold bitOf; split
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem msRoundG_lt (c : Cfg) (htab : 0 < c.tab) (k : Nat) (st : RSt)
    (v : Nat) (g : Nat → Nat → Nat) :
    (msRoundG c k st v g).bad < M ∧ (msRoundG c k st v g).lb < M ∧
      (msRoundG c k st v g).lam < M ∧ (msRoundG c k st v g).idx < c.tab ∧
      (msRoundG c k st v g).bs < M ∧ (msRoundG c k st v g).mx < M ∧
      (msRoundG c k st v g).cell < M ∧ (msRoundG c k st v g).acc < M ∧
      (msRoundG c k st v g).sc < M ∧ (msRoundG c k st v g).muQ < M :=
  ⟨MA_lt _ _, MS_lt _ _, MA_lt _ _, Nat.mod_lt _ htab, MA_lt _ _, MA_lt _ _,
   MA_lt _ _, MA_lt _ _, MA_lt _ _, MA_lt _ _⟩

private theorem msRoundG_arr (c : Cfg) (k : Nat) (st : RSt) (v : Nat)
    (g : Nat → Nat → Nat) :
    (msRoundG c k st v g).arr = g ((msRoundG c k st v g).cell) := rfl

private theorem msRoundG_sc_eq (c : Cfg) (k : Nat) (st : RSt) (v : Nat)
    (g : Nat → Nat → Nat) :
    (msRoundG c k st v g).sc =
      semScanS (MMul st.sc (bitOf (k % c.B ≠ 0)))
        (MMul (k % c.B + 2) (k % c.B + 2)) (c.n0 + k / c.B) (k % c.B + 2)
        (bitOf (k % c.B < c.B - 2)) := rfl

/-- The scan register only ever holds `0` or a trial divisor `d ≥ 2`. -/
private theorem semScanS_scan {S sq n d w : Nat} (hS : S < M) (hd : d < M)
    (h2 : 2 ≤ d) (hw : w = 0 ∨ w = 1) (hsc : S = 0 ∨ 2 ≤ S) :
    semScanS S sq n d w = 0 ∨ 2 ≤ semScanS S sq n d w := by
  have hg : semScanG S sq n d w = 0 ∨ semScanG S sq n d w = 1 := by
    unfold semScanG
    rcases hw with rfl | rfl
    · exact Or.inl (MMul_zero_right _)
    · rw [MMul_bit_one]; exact bitOf_zero_or_one _
  unfold semScanS
  rcases hg with hg0 | hg1
  · rw [hg0, MS_one_zero, MMul_zero_left, MMul_one_left hS, MA_zero_right hS]
    exact hsc
  · rw [hg1, MS_one_one, MMul_zero_left, MMul_one_left hd, MA_zero_left hd]
    exact Or.inr h2

/-- Clearing the scan at `r = 0` keeps the invariant. -/
private theorem MMul_bit_scan {s : Nat} (hs : s < M) (hsc : s = 0 ∨ 2 ≤ s)
    (p : Prop) [Decidable p] :
    MMul s (bitOf p) = 0 ∨ 2 ≤ MMul s (bitOf p) := by
  by_cases hp : p
  · rw [bitOf_pos hp, MMul_one_right hs]; exact hsc
  · rw [bitOf_neg hp, MMul_zero_right]; exact Or.inl rfl

/-- **The boundary invariant is preserved by a round.** -/
theorem msRound_BInv (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (st : RSt) (h : BInv c st) : BInv c (msRound c k st) := by
  obtain ⟨hbad, hlb, hlam, hidx, hbs, hmx, hcell, hacc, hscM, hmuQ, harr, hscan⟩ := h
  obtain ⟨hkM, hkdiv, hrB, hnlim⟩ := ok_idx hok hk
  have hdM : k % c.B + 2 < M := by
    have h1 := ok_Blt hok
    have h2 := two20_lt_M
    omega
  rw [msRound_eq_G]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
    msRoundG_lt c (ok_tab0 hok) k st (st.arr (msIdx c k st))
      (fun cl j => if j = c.n0 + k / c.B then cl else st.arr j)
  refine ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, ?_, ?_⟩
  · intro i
    rw [msRoundG_arr]
    split
    · exact g7
    · exact harr i
  · rw [msRoundG_sc_eq]
    exact semScanS_scan (MMul_lt _ _) hdM (by omega) (bitOf_zero_or_one _)
      (MMul_bit_scan hscM hscan _)

/-! ## One block of `B` rounds is one candidate -/

private theorem semI_work (qq q lim idx : Nat) (hqq : qq < M) :
    semI 1 qq 0 q 0 lim idx = qq := by
  unfold semI
  rw [MMul_one_left hqq, MMul_zero_left, MMul_zero_left, MA_zero_right hqq,
    MA_zero_right hqq]

private theorem semMuQ_zero (x v : Nat) (hx : x < M) : semMuQ 0 x v = x := by
  unfold semMuQ
  rw [MS_one_zero, MMul_one_left hx, MMul_zero_left, MA_zero_right hx]

private theorem semLb_zero (x mun n : Nat) (hx : x < M) : semLb x mun 0 n = x := by
  unfold semLb
  simp only [MMul_zero_right, MMul_zero_left]
  rw [MA_zero_right hx]
  unfold MS
  rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

private theorem semLam_zero (x ho n : Nat) (hx : x < M) : semLam x ho n 0 = x := by
  unfold semLam
  rw [MMul_zero_right, MMul_zero_left, MA_zero_right hx]

private theorem semBadRow_zero (x ok fire : Nat) (hx : x < M) :
    semBadRow x ok fire 0 = x := by
  unfold semBadRow
  simp only [MMul_zero_right]
  exact MA_zero_right hx

private theorem semBadC_zero (x star ab lam cs cl cg : Nat) (hx : x < M) :
    semBadC x star ab lam cs cl cg 0 = x := by
  unfold semBadC
  rw [MMul_zero_right, MA_zero_right hx]

private theorem semBadW_zero (x acc ab cs cl : Nat) (hx : x < M) :
    semBadW x acc ab cs cl 0 = x := by
  unfold semBadW
  rw [MMul_zero_right, MA_zero_right hx]

private theorem semBadRow_lt (bad ok fire cc : Nat) :
    semBadRow bad ok fire cc < M := by
  unfold semBadRow
  exact MA_lt _ _

private theorem semCell_zero (mun ab x : Nat) (hx : x < M) :
    semCell mun ab 0 x = x := by
  unfold semCell
  rw [MMul_zero_right, MS_one_zero, MMul_one_left hx, MA_zero_left hx]

private theorem semMax_zero (fire mx x : Nat) (hx : x < M) :
    semMax fire mx 0 x = x := by
  unfold semMax
  simp only [MMul_zero_right]
  rw [MS_one_zero, MMul_one_left hx, MA_zero_left hx]

private theorem semBs_zero (n fire x : Nat) (hx : x < M) :
    semBs n fire x 0 = x := by
  unfold semBs
  rw [MMul_zero_right, MS_one_zero, MMul_one_left hx, MA_zero_left hx]

private theorem semIdx_zero (x fire tab : Nat) (hx : x < tab) (hxM : x < M) :
    semIdx x 0 fire tab = x := by
  unfold semIdx
  rw [MMul_zero_left, MA_zero_right hxM]
  exact Nat.mod_eq_of_lt hx

private theorem semScanS_zero (S sq n d : Nat) (hS : S < M) :
    semScanS S sq n d 0 = S := by
  unfold semScanS semScanG
  rw [MMul_zero_right, MS_one_zero, MMul_one_left hS, MMul_zero_left,
    MA_zero_right hS]

private theorem semAcc_zero (acc ab qq sq : Nat) (hacc : acc < M) :
    semAcc acc ab qq sq 0 = acc := by
  unfold semAcc
  rw [MMul_zero_right, MA_zero_right hacc]

private theorem semI_mobius (qq q lim idx : Nat) (hq : q < M) :
    semI 0 qq 1 q 0 lim idx = q := by
  unfold semI
  rw [MMul_zero_left, MMul_one_left hq, MA_zero_left hq, MMul_zero_left,
    MA_zero_right hq]

private theorem semMuQ_one (x v : Nat) (hv : v < M) : semMuQ 1 x v = v := by
  unfold semMuQ
  rw [MS_one_one, MMul_zero_left, MMul_one_left hv, MA_zero_left hv]

private theorem semI_commit (qq q lim idx : Nat) :
    semI 0 qq 0 q 1 lim idx = MA lim idx := by
  unfold semI
  rw [MMul_zero_left, MMul_zero_left, MMul_one_left (MA_lt _ _),
    MA_zero_zero, MA_zero_left (MA_lt _ _)]

/-- The candidate-level effect of the final round, stated in the same named
semantic quantities as `msRound`.  Keeping this separate prevents the block
proof from expanding both 107-instruction rounds at once. -/
private def commitStep (c : Cfg) (n : Nat) (st : St)
    (acc sc muQ : Nat) : St :=
  let p := semP sc n
  let qn := semQ sc n
  let vlog := st.arr (c.limit + 1 + st.idx)
  let mun := semMun qn p muQ
  let lb1 := semLb st.lb mun 1 n
  let absN := semAbsN lb1
  let star := semStar acc absN n
  let mx1 := semMx st.mx star
  let fire := semFire n c.limit st.bs
  let lam1 := semLam st.lam c.handoff n 1
  let ok := semOk (MMul 5 (semCv n star st.mx))
    (semLU n c.handoff vlog lam1)
  let cell1 := semCell mun absN 1 st.cell
  { bad := semBadC (semBadRow st.bad ok fire 1) star absN lam1
      c.capS c.capL c.capLog 1
  , lb := lb1
  , lam := lam1
  , idx := semIdx st.idx 1 fire c.tab
  , bs := semBs n fire st.bs 1
  , mx := semMax fire mx1 1 st.mx
  , cell := cell1
  , arr := fun j => if j = n then cell1 else st.arr j }

private theorem msRound_commit (c : Cfg) (hok : msOK c = true) (q : Nat)
    (_hq : q < c.len) (st : RSt) (h : BInv c st) :
    toSt (msRound c (q * c.B + (c.B - 1)) st) =
      commitStep c (c.n0 + q) (toSt st) st.acc st.sc st.muQ := by
  obtain ⟨hbad, hlb, hlam, hidx, hbs, hmx, hcell, hacc, hscM, hmuQ, harr, hscan⟩ := h
  have hr : c.B - 1 < c.B := by have := ok_B3 hok; omega
  obtain ⟨hmod, hdiv⟩ := idx_decode c.B q (c.B - 1) (ok_B_pos hok) hr
  have hr0 : c.B - 1 ≠ 0 := by have := ok_B3 hok; omega
  have hlogM : c.limit + 1 + st.idx < M := by
    have hlim := ok_lim32 hok
    have htab := ok_tab hok
    have hcap : (2 : Nat) ^ 32 + 1 + 2 ^ 10 < M := by decide
    omega
  have hload : MA (c.limit + 1) st.idx = c.limit + 1 + st.idx :=
    Nat.mod_eq_of_lt hlogM
  have htrue : bitOf True = 1 := bitOf_pos True.intro
  simp only [msRound, toSt, commitStep, hmod, hdiv,
    bitOf_pos hr0, bitOf_neg (show ¬ c.B - 1 < c.B - 2 by omega),
    bitOf_neg (show ¬ c.B - 1 = c.B - 2 by omega), htrue,
    MMul_one_right hscM, MMul_one_right hacc,
    semScanS_zero _ _ _ _ hscM, semAcc_zero _ _ _ _ hacc,
    semI_commit, hload, semMuQ_zero _ _ hmuQ]
  rw [semBadW_zero _ _ _ _ _ (semBadRow_lt _ _ _ _)]

private theorem semLb_one (lb mun n : Nat) :
    semLb lb mun 1 n =
      MS (MA lb (MMul (bitOf (mun = 2)) (semDn n)))
        (MMul (bitOf (mun = 0)) (semDn n)) := by
  unfold semLb
  rw [MMul_bit_one, MMul_bit_one]

private theorem semLam_one (lam ho n : Nat) :
    semLam lam ho n 1 = MA lam (MMul (bitOf (ho ≤ n)) (RS62.incUWord n)) := by
  unfold semLam
  rw [MMul_bit_one]

private theorem semBadRow_one (bad ok fire : Nat) :
    semBadRow bad ok fire 1 = MA bad (MMul (MS 1 ok) fire) := by
  unfold semBadRow
  rw [MMul_one_right (MMul_lt _ _)]

private theorem semBadC_one (bad star absN lam cs cl cg : Nat) :
    semBadC bad star absN lam cs cl cg 1 =
      MA bad (bitOf (cs < star ∨ cl < absN ∨ cg < lam)) := by
  unfold semBadC
  rw [MMul_bit_one]
  have hb : bitOf ((cs < star ∨ cl < absN) ∨ cg < lam) =
      bitOf (cs < star ∨ cl < absN ∨ cg < lam) := by
    apply bitOf_congr
    constructor
    · rintro ((hs | hl) | hg)
      · exact Or.inl hs
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr hg)
    · rintro (hs | hl | hg)
      · exact Or.inl (Or.inl hs)
      · exact Or.inl (Or.inr hl)
      · exact Or.inr hg
  rw [hb]

private theorem semCell_one (mun absN cell : Nat) :
    semCell mun absN 1 cell = MA (MMul pack mun) absN := by
  unfold semCell
  rw [MMul_one_right (MA_lt _ _), MS_one_one, MMul_zero_left,
    MA_zero_right (MA_lt _ _)]

private theorem semMax_one (fire mx mx0 : Nat) :
    semMax fire mx 1 mx0 = MMul (MS 1 fire) mx := by
  unfold semMax
  rw [MMul_one_right (MMul_lt _ _), MS_one_one, MMul_zero_left,
    MA_zero_right (MMul_lt _ _)]

private theorem semBs_one (n fire bs : Nat) :
    semBs n fire bs 1 =
      MA (MMul 64 (bitOf (n < 64)))
        (MMul (MS 1 (bitOf (n < 64)))
          (MA (MMul (MA 1 n) fire) (MMul (MS 1 fire) bs))) := by
  unfold semBs semSmall semBsIn
  rw [MMul_one_right (MA_lt _ _), MS_one_one, MMul_zero_left,
    MA_zero_right (MA_lt _ _)]
  rw [MMul_comm (MA (MMul (MA 1 n) fire) (MMul (MS 1 fire) bs))]

private theorem semIdx_one (idx fire tab : Nat) (hfire : fire < M) :
    semIdx idx 1 fire tab = MA idx fire % tab := by
  unfold semIdx
  rw [MMul_one_left hfire]

private theorem commitStep_work (c : Cfg) (n : Nat) (st : RSt)
    (w : Nat × Nat × Nat) (hw : w = workFold c st.arr n st.bad)
    (hsc : w.2.2 < M) (hn : n < M) :
    commitStep c n
        { bad := w.1, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs,
          mx := st.mx, cell := st.cell, arr := st.arr }
        w.2.1 w.2.2 (semMu1 (st.arr (semQ w.2.2 n))) =
      msStep c n (toSt st) := by
  have hp : semP w.2.2 n = if w.2.2 = 0 then n else w.2.2 := semP_eq hsc hn
  have hfire : semFire n c.limit st.bs =
      bitOf (n < 64 ∨ n = c.limit ∨ MA 1 n = MMul 2 st.bs) := by
    unfold semFire
    apply bitOf_congr
    constructor
    · rintro ((hs | hl) | hd)
      · exact Or.inl hs
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr hd)
    · rintro (hs | hl | hd)
      · exact Or.inl (Or.inl hs)
      · exact Or.inl (Or.inr hl)
      · exact Or.inr hd
  subst w
  apply St.ext <;> simp only [commitStep, msStep, toSt, hp, hfire,
    semQ, semMu1, semMun, semSqdiv, semLb_one, semDn, semAbsN, semBge,
    semStar, semMx, semGt, semCv, semSmall, semLam_one, semLU, semLo,
    semOk, semBadRow_one, semBadC_one, semIdx_one _ _ _ (bitOf_lt _), semBs_one,
    semMax_one, semCell_one] <;> rfl

/-- A round strictly inside the work window is exactly one `workRound`; all
candidate-level fields are framed and the unconditional store repeats the
previous candidate's packed cell. -/
private theorem msRound_work (c : Cfg) (hok : msOK c = true) (q r : Nat)
    (hq : q < c.len) (hr : r < c.B - 2) (st : RSt) (h : BInv c st) :
    msRound c (q * c.B + r) st =
      let w := workRound c st.arr (c.n0 + q)
        (st.bad, MMul st.acc (bitOf (r ≠ 0)), MMul st.sc (bitOf (r ≠ 0))) r
      { bad := w.1, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs,
        mx := st.mx, cell := st.cell, acc := w.2.1, sc := w.2.2, muQ := st.muQ,
        arr := fun j => if j = c.n0 + q then st.cell else st.arr j } := by
  obtain ⟨hbad, hlb, hlam, hidx, hbs, hmx, hcell, hacc, hscM, hmuQ, harr, hscan⟩ := h
  have hB : 0 < c.B := ok_B_pos hok
  have hrB : r < c.B := by omega
  obtain ⟨hmod, hdiv⟩ := idx_decode c.B q r hB hrB
  simp only [msRound, workRound, hmod, hdiv]
  rw [bitOf_pos hr, bitOf_neg (show ¬ r = c.B - 2 by omega),
    bitOf_neg (show ¬ r = c.B - 1 by omega)]
  let S0 := MMul st.sc (bitOf (r ≠ 0))
  let sq := MMul (r + 2) (r + 2)
  let n := c.n0 + q
  let d := r + 2
  let g := bitOf (S0 = 0 ∧ sq ≤ n ∧ n % d = 0)
  have hsqM : sq < M := MMul_lt _ _
  have hqqM : n / sq < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by
    have hqle : c.n0 + q ≤ c.limit := by
      have hlim := ok_limit hok
      omega
    exact Nat.lt_of_le_of_lt hqle (ok_limM hok))
  have hI : semI 1 (n / sq) 0
      (semQ (semScanS S0 sq n d 1) n) 0 (c.limit + 1) st.idx = n / sq :=
    semI_work _ _ _ _ hqqM
  have hg : bitOf (((S0 = 0 ∧ sq ≤ n) ∧ n % d = 0)) = g := by
    apply bitOf_congr
    simp only [and_assoc]
  have hScan : semScanS S0 sq n d 1 =
      MA (MMul (MS 1 g) S0) (MMul g d) := by
    unfold semScanS semScanG
    rw [MMul_one_right (bitOf_lt _), hg]
  have hI' : semI 1 (n / sq) 0
      (semQ (MA (MMul (MS 1 g) S0) (MMul g d)) n) 0
        (c.limit + 1) st.idx = n / sq := by
    rw [← hScan]
    exact hI
  have hmu (v : Nat) : semMuQ 0 st.muQ v = st.muQ :=
    semMuQ_zero _ _ hmuQ
  have hlb0 (x : Nat) : semLb st.lb x 0 n = st.lb := semLb_zero _ _ _ hlb
  have hlam0 : semLam st.lam c.handoff n 0 = st.lam :=
    semLam_zero _ _ _ hlam
  have hidxM : st.idx < M := by
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hidx (ok_tab hok)) (by decide)
  have hidx0 (fire : Nat) : semIdx st.idx 0 fire c.tab = st.idx :=
    semIdx_zero _ _ _ hidx hidxM
  have hbs0 (fire : Nat) : semBs n fire st.bs 0 = st.bs :=
    semBs_zero _ _ _ hbs
  have hmax0 (fire mx : Nat) : semMax fire mx 0 st.mx = st.mx :=
    semMax_zero _ _ _ hmx
  have hcell0 (mun ab : Nat) : semCell mun ab 0 st.cell = st.cell :=
    semCell_zero _ _ _ hcell
  have hrow0 (ok fire : Nat) : semBadRow st.bad ok fire 0 = st.bad :=
    semBadRow_zero _ _ _ hbad
  have hbadW (acc ab : Nat) : semBadW st.bad acc ab c.capS c.capL 1 =
      MA st.bad (bitOf (c.capS < acc ∨ c.capL < ab)) := by
    unfold semBadW
    rw [MMul_one_right (bitOf_lt _)]
  have hbadC (acc ab star absN lam : Nat) :
      semBadC (semBadW st.bad acc ab c.capS c.capL 1)
        star absN lam c.capS c.capL c.capLog 0 =
        MA st.bad (bitOf (c.capS < acc ∨ c.capL < ab)) := by
    calc
      _ = semBadW st.bad acc ab c.capS c.capL 1 :=
        semBadC_zero _ _ _ _ _ _ _ (MA_lt _ _)
      _ = _ := hbadW acc ab
  ext j <;> simp only [S0, sq, n, d, g, hScan, hI', hmu, hlb0, hlam0,
    hidx0, hbs0, hmax0, hcell0, hrow0, hbadC, semAcc, semAbs, semMu1]

private theorem msRound_mobius (c : Cfg) (hok : msOK c = true) (q : Nat)
    (hq : q < c.len) (st : RSt) (h : BInv c st) :
    msRound c (q * c.B + (c.B - 2)) st =
      { bad := st.bad, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs,
        mx := st.mx, cell := st.cell, acc := st.acc, sc := st.sc,
        muQ := semMu1 (st.arr (semQ st.sc (c.n0 + q))),
        arr := fun j => if j = c.n0 + q then st.cell else st.arr j } := by
  obtain ⟨hbad, hlb, hlam, hidx, hbs, hmx, hcell, hacc, hscM, hmuQ, harr, hscan⟩ := h
  have hr : c.B - 2 < c.B := by have := ok_B3 hok; omega
  obtain ⟨hmod, hdiv⟩ := idx_decode c.B q (c.B - 2) (ok_B_pos hok) hr
  have hr0 : c.B - 2 ≠ 0 := by have := ok_B3 hok; omega
  have hqM : semQ st.sc (c.n0 + q) < M := by
    unfold semQ
    have hnle : c.n0 + q ≤ c.limit := by have := ok_limit hok; omega
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt hnle (ok_limM hok))
  have htrue : bitOf True = 1 := bitOf_pos True.intro
  have hmu1 : semMu1 (st.arr (semQ st.sc (c.n0 + q))) < M := by
    unfold semMu1
    exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (harr _)
  simp only [msRound, hmod, hdiv, bitOf_pos hr0,
    bitOf_neg (show ¬ c.B - 2 < c.B - 2 by omega), htrue,
    bitOf_neg (show ¬ c.B - 2 = c.B - 1 by omega),
    MMul_one_right hscM, MMul_one_right hacc,
    semScanS_zero _ _ _ _ hscM, semAcc_zero _ _ _ _ hacc,
    semI_mobius _ _ _ _ hqM, semMuQ_one _ _ hmu1]
  have hidxM : st.idx < M :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hidx (ok_tab hok)) (by decide)
  ext j <;> simp only [semLb_zero _ _ _ hlb, semLam_zero _ _ _ hlam,
    semIdx_zero _ _ _ hidx hidxM, semBs_zero _ _ _ hbs,
    semMax_zero _ _ _ hmx, semCell_zero _ _ _ hcell,
    semBadRow_zero _ _ _ hbad, semBadC_zero _ _ _ _ _ _ _ hbad,
    semBadW, MMul_zero_right, MA_zero_right hbad]

private def workState (st : RSt) (n : Nat) (w : Nat × Nat × Nat) : RSt :=
  { bad := w.1, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs,
    mx := st.mx, cell := st.cell, acc := w.2.1, sc := w.2.2, muQ := st.muQ,
    arr := fun j => if j = n then st.cell else st.arr j }

private theorem flat_lt (B len q r : Nat) (hq : q < len) (hr : r < B) :
    q * B + r < len * B := by
  have hq1 : q + 1 ≤ len := by omega
  have hm := Nat.mul_le_mul_right B hq1
  have hs : q * B + r < (q + 1) * B := by
    rw [Nat.add_mul]
    omega
  exact Nat.lt_of_lt_of_le hs hm

private theorem prefix_inv (c : Cfg) (hok : msOK c = true) (q m : Nat)
    (hq : q < c.len) (hm : m ≤ c.B) (st : RSt) (h : BInv c st) :
    BInv c ((List.range m).foldl
      (fun x r => msRound c (q * c.B + r) x) st) := by
  induction m with
  | zero => exact h
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      apply msRound_BInv c hok (q * c.B + m)
      · exact flat_lt _ _ _ _ hq (by omega)
      · exact ih (by omega)

private theorem work_prefix (c : Cfg) (hok : msOK c = true) (q m : Nat)
    (hq : q < c.len) (hm1 : 1 ≤ m) (hm : m ≤ c.B - 2)
    (st : RSt) (h : BInv c st) :
    (List.range m).foldl (fun x r => msRound c (q * c.B + r) x) st =
      workState st (c.n0 + q)
        ((List.range m).foldl (workRound c st.arr (c.n0 + q))
          (st.bad, 0, 0)) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp only [List.range_succ, List.range_zero, List.foldl_append,
          List.foldl_nil, List.foldl_cons]
        rw [msRound_work c hok q 0 hq (by omega) st h]
        simp only [bitOf_neg (show ¬ ((0 : Nat) ≠ 0) by simp), MMul_zero_right]
        rfl
      · rw [List.range_succ, List.foldl_append, ih (by omega) (by omega)]
        let w := (List.range m).foldl (workRound c st.arr (c.n0 + q))
          (st.bad, 0, 0)
        let base : RSt :=
          { bad := w.1, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs,
            mx := st.mx, cell := st.cell, acc := w.2.1, sc := w.2.2,
            muQ := st.muQ, arr := st.arr }
        have hcur : workState st (c.n0 + q) w =
            { base with arr := fun j => if j = c.n0 + q then st.cell else base.arr j } := rfl
        have hi := prefix_inv c hok q m hq (by omega) st h
        rw [ih (by omega) (by omega)] at hi
        have hb : BInv c base := by
          obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12⟩ := hi
          exact ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,h.2.2.2.2.2.2.2.2.2.2.1,a12⟩
        have hb0 := hb
        obtain ⟨_, _, _, hbidx, _, _, _, hbacc, hbscM, _, _, hbscan⟩ := hb
        have hdivm : (q * c.B + m) / c.B = q :=
          (idx_decode c.B q m (ok_B_pos hok) (by omega)).2
        have hind : msRound c (q * c.B + m)
              { base with arr := fun j => if j = c.n0 + q then st.cell else base.arr j } =
            msRound c (q * c.B + m) base := by
          simpa only [hdivm] using msRound_arr_indep c hok (q * c.B + m)
            (flat_lt _ _ _ _ hq (by omega)) base hbidx hbscan hbscM st.cell
        simp only [List.foldl_cons, List.foldl_nil, List.foldl_append]
        rw [hcur, hind, msRound_work c hok q m hq (by omega) base hb0]
        simp only [base, workState, w, bitOf_pos hm0, MMul_one_right hbacc,
          MMul_one_right hbscM]

/--
**The re-blocking, at one block.**  The statement mentions no problem size.

Rounds `r < B − 2` carry the trial scan and the `w`-terms (`workFold`), round
`B − 2` latches `μ(q)`, round `B − 1` commits — and the three registers a
candidate consumes (`rAcc`, `rS`, `rMuQ`) are cleared or overwritten inside
the block, so the incoming values are irrelevant and `toSt` is enough.
-/
theorem block_eq_msStep (c : Cfg) (hok : msOK c = true) (q : Nat) (hq : q < c.len)
    (st : RSt) (h : BInv c st) :
    toSt (block c.B (fun x r => msRound c r x) st q)
      = msStep c (c.n0 + q) (toSt st) := by
  have hB3 := ok_B3 hok
  have hrange : List.range c.B = List.range (c.B - 2) ++ [c.B - 2, c.B - 1] := by
    rw [show c.B = (c.B - 2) + 2 by omega]
    rw [List.range_succ, List.range_succ, List.append_assoc]
    rfl
  have hm1 : 1 ≤ c.B - 2 := by omega
  let n := c.n0 + q
  let w := workFold c st.arr n st.bad
  let pre := workState st n w
  have hpre : BInv c pre := by
    have hi := prefix_inv c hok q (c.B - 2) hq (by omega) st h
    rw [work_prefix c hok q (c.B - 2) hq hm1 (Nat.le_refl _) st h] at hi
    simpa only [pre, w, n, workFold] using hi
  rw [block_eq_shift, hrange, List.foldl_append,
    work_prefix c hok q (c.B - 2) hq hm1 (Nat.le_refl _) st h]
  simp only [List.foldl_cons, List.foldl_nil]
  have hbm : c.B - 2 < c.B := by omega
  have hbc : c.B - 1 < c.B := by omega
  have hkm : q * c.B + (c.B - 2) < c.len * c.B :=
    flat_lt _ _ _ _ hq hbm
  have hkc : q * c.B + (c.B - 1) < c.len * c.B :=
    flat_lt _ _ _ _ hq hbc
  have hdivm := (idx_decode c.B q (c.B - 2) (ok_B_pos hok) hbm).2
  have hdivc := (idx_decode c.B q (c.B - 1) (ok_B_pos hok) hbc).2
  have harr0 : ∀ i, st.arr i < M := h.2.2.2.2.2.2.2.2.2.2.1
  let preBase : RSt :=
    { bad := w.1, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs,
      mx := st.mx, cell := st.cell, acc := w.2.1, sc := w.2.2,
      muQ := st.muQ, arr := st.arr }
  have hpbase : BInv c preBase := by
    obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,_,a12⟩ := hpre
    exact ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,harr0,a12⟩
  have hpbase0 := hpbase
  obtain ⟨_,_,_,hpidx,_,_,_,_,hpsc,_,_,hpscan⟩ := hpbase0
  have hindm : msRound c (q * c.B + (c.B - 2)) pre =
      msRound c (q * c.B + (c.B - 2)) preBase := by
    simpa only [pre, preBase, workState, hdivm, n] using
      msRound_arr_indep c hok (q * c.B + (c.B - 2)) hkm preBase
        hpidx hpscan hpsc st.cell
  let mobBase : RSt :=
    { bad := w.1, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs,
      mx := st.mx, cell := st.cell, acc := w.2.1, sc := w.2.2,
      muQ := semMu1 (st.arr (semQ w.2.2 n)), arr := st.arr }
  have hmobEq : msRound c (q * c.B + (c.B - 2)) pre =
      { mobBase with arr := fun j => if j = n then st.cell else mobBase.arr j } := by
    rw [hindm, msRound_mobius c hok q hq preBase hpbase]
  have hmobRun := msRound_BInv c hok _ hkm pre hpre
  rw [hmobEq] at hmobRun
  have hmob : BInv c mobBase := by
    obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,_,a12⟩ := hmobRun
    exact ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,harr0,a12⟩
  have hmob0 := hmob
  obtain ⟨_,_,_,hmidx,_,_,_,_,hmsc,_,_,hmscan⟩ := hmob0
  have hind : msRound c (q * c.B + (c.B - 1))
        { mobBase with arr := fun j => if j = n then st.cell else mobBase.arr j } =
      msRound c (q * c.B + (c.B - 1)) mobBase := by
    simpa only [hdivc, n] using msRound_arr_indep c hok
      (q * c.B + (c.B - 1)) hkc mobBase hmidx hmscan hmsc st.cell
  change toSt (msRound c (q * c.B + (c.B - 1))
    (msRound c (q * c.B + (c.B - 2)) pre)) = _
  rw [hmobEq, hind, msRound_commit c hok q hq mobBase hmob]
  have hnM : n < M := by
    have hnle : n ≤ c.limit := by
      have := ok_limit hok
      omega
    exact Nat.lt_of_le_of_lt hnle (ok_limM hok)
  exact commitStep_work c n st w rfl hmsc hnM

/-! ## The initialization block -/

private def initMovs (c : Cfg) : List Instr :=
  [ .mov rLb (.lit (bias + fpDlit)), .mov rLam (.lit c.seed),
    .mov rBs (.lit 64), .mov rCell (.lit c.cell1), .mov rMuQ (.lit 2),
    .mov rT1 (.lit 1), .mov rT2 (.lit c.cell1) ]

private def storeTriple (e : Nat × Nat) : List AInstr :=
  [ .scalar (.mov rT1 (.lit e.1)), .scalar (.mov rT2 (.lit e.2)),
    .store rT1 rT2 ]

private def logRows (c : Cfg) : List (Nat × Nat) :=
  c.logs.map (fun e => (c.limit + 1 + e.1, e.2))

private theorem msInit_eq (c : Cfg) :
    msInit c = lift (initMovs c) ++
      ([.store rT1 rT2] ++ (logRows c).flatMap storeTriple) := by
  simp only [msInit, initMovs, logRows, List.flatMap_map]
  rfl

private theorem storeTriple_regs (k : Nat) (e : Nat × Nat) (s : AState) (j : Nat) :
    (arun k s (storeTriple e)).regs j =
      (if j = rT2 then e.2 % M else if j = rT1 then e.1 % M else s.regs j) := rfl

private theorem storeTriple_arr (k : Nat) (e : Nat × Nat) (s : AState) (i : Nat) :
    (arun k s (storeTriple e)).arr i =
      (if i = e.1 % M then e.2 % M else s.arr i) := rfl

private theorem find?_snoc_none {α : Type _} {p : α → Bool} {a : α} :
    ∀ {l : List α}, l.find? p = none →
      (l ++ [a]).find? p = (if p a then some a else none) := by
  intro l
  induction l with
  | nil =>
      intro _
      simp only [List.nil_append]
      by_cases ha : p a
      · rw [List.find?_cons_of_pos ha, if_pos ha]
      · rw [List.find?_cons_of_neg ha, if_neg ha]
        rfl
  | cons b l ih =>
      intro h
      by_cases hb : p b
      · rw [List.find?_cons_of_pos hb] at h
        exact absurd h (by simp)
      · rw [List.cons_append, List.find?_cons_of_neg hb,
          ih (by rw [List.find?_cons_of_neg hb] at h; exact h)]

private theorem find?_snoc_some {α : Type _} {p : α → Bool} {a x : α} :
    ∀ {l : List α}, l.find? p = some x → (l ++ [a]).find? p = some x := by
  intro l
  induction l with
  | nil => intro h; exact absurd h (by simp)
  | cons b l ih =>
      intro h
      by_cases hb : p b
      · rw [List.find?_cons_of_pos hb] at h
        rw [List.cons_append, List.find?_cons_of_pos hb]
        exact h
      · rw [List.find?_cons_of_neg hb] at h
        rw [List.cons_append, List.find?_cons_of_neg hb]
        exact ih h

private theorem stores_arr (k : Nat) :
    ∀ (l : List (Nat × Nat)) (s : AState) (i : Nat), (∀ e ∈ l, e.1 < M) →
      (arun k s (l.flatMap storeTriple)).arr i =
        ((l.reverse.find? (fun e => decide (e.1 = i))).map
          (fun e => e.2 % M)).getD (s.arr i) := by
  intro l
  induction l with
  | nil => intro s i _; rfl
  | cons e l ih =>
      intro s i hall
      have hmem : ∀ f ∈ l, f.1 < M :=
        fun f hf => hall f (List.mem_cons_of_mem e hf)
      have he : e.1 < M := hall e (List.mem_cons_self ..)
      show (arun k (arun k s (storeTriple e)) (l.flatMap storeTriple)).arr i = _
      rw [ih _ i hmem, storeTriple_arr, Nat.mod_eq_of_lt he,
        show (e :: l).reverse = l.reverse ++ [e] from by simp]
      cases hfind : l.reverse.find? (fun f => decide (f.1 = i)) with
      | some x => rw [find?_snoc_some hfind]; simp
      | none =>
          rw [find?_snoc_none hfind]
          by_cases hi : e.1 = i
          · subst i; simp
          · rw [if_neg (fun h' : i = e.1 => hi h'.symm)]
            simp [hi]

private theorem stores_regs (k : Nat) :
    ∀ (l : List (Nat × Nat)) (s : AState) (j : Nat), j ≠ rT1 → j ≠ rT2 →
      (arun k s (l.flatMap storeTriple)).regs j = s.regs j := by
  intro l
  induction l with
  | nil => intro s j _ _; rfl
  | cons e l ih =>
      intro s j h1 h2
      show (arun k (arun k s (storeTriple e)) (l.flatMap storeTriple)).regs j = _
      rw [ih _ j h1 h2, storeTriple_regs, if_neg h2, if_neg h1]

private theorem stores_regs_lt (k : Nat) :
    ∀ (l : List (Nat × Nat)) (s : AState), (∀ j, s.regs j < M) →
      ∀ j, (arun k s (l.flatMap storeTriple)).regs j < M := by
  intro l
  induction l with
  | nil => intro s h j; exact h j
  | cons e l ih =>
      intro s h j
      refine ih (arun k s (storeTriple e)) ?_ j
      intro j'
      rw [storeTriple_regs]
      split
      · exact Nat.mod_lt _ M_pos
      · split
        · exact Nat.mod_lt _ M_pos
        · exact h j'

private theorem stores_defined (c : Cfg) (hok : msOK c = true) (k : Nat) :
    ∀ (l : List (Nat × Nat)) (s : AState),
      (∀ e ∈ l, e.1 < c.limit + 1 + c.tab) →
      AllDefined (c.limit + 1 + c.tab) k s (l.flatMap storeTriple) := by
  intro l
  induction l with
  | nil => intro s _; trivial
  | cons e l ih =>
      intro s hall
      have he := hall e (List.mem_cons_self ..)
      have heM : e.1 < M := by
        have hlim := ok_lim32 hok
        have htab := ok_tab hok
        have hcap : (2 : Nat) ^ 32 + 1 + 2 ^ 10 < M := by decide
        omega
      rw [List.flatMap_cons, AllDefined_append]
      refine ⟨⟨trivial, trivial, ?_, trivial⟩, ih _ ?_⟩
      · change (if rT1 = rT2 then e.2 % M else
          if rT1 = rT1 then e.1 % M else s.regs rT1) < c.limit + 1 + c.tab
        rw [if_neg (by decide), if_pos rfl, Nat.mod_eq_of_lt heM]
        exact he
      · intro f hf
        exact hall f (List.mem_cons_of_mem e hf)

private theorem logRows_mem (c : Cfg) (hok : msOK c = true) :
    ∀ e ∈ logRows c, e.1 < c.limit + 1 + c.tab := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  have hall := ok_logs hok
  rw [List.all_eq_true] at hall
  have hxok := hall x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hxok
  omega

private theorem logRows_mem_M (c : Cfg) (hok : msOK c = true) :
    ∀ e ∈ logRows c, e.1 < M := by
  intro e he
  have haddr := logRows_mem c hok e he
  have hlim := ok_lim32 hok
  have htab := ok_tab hok
  have hcap : (2 : Nat) ^ 32 + 1 + 2 ^ 10 < M := by decide
  omega

private theorem msInit_defined (c : Cfg) (hok : msOK c = true) :
    AllDefined (c.limit + 1 + c.tab) 0 initialAState (msInit c) := by
  rw [msInit_eq, AllDefined_append]
  refine ⟨allDefined_lift_of_noDiv _ _ _ _ rfl, ?_⟩
  rw [AllDefined_append]
  refine ⟨⟨?_, trivial⟩, stores_defined c hok 0 (logRows c) _ (logRows_mem c hok)⟩
  change (arun 0 initialAState (lift (initMovs c))).regs rT1 < c.limit + 1 + c.tab
  rw [arun_lift_regs]
  change 1 % M < c.limit + 1 + c.tab
  rw [Nat.mod_eq_of_lt one_lt_M]
  have := ok_n0 hok
  have := ok_tab0 hok
  omega

/-- The state the initialization block reaches. -/
def msEntryA (c : Cfg) : AState := arun 0 initialAState (msInit c)

theorem msInit_reaches (c : Cfg) (hok : msOK c = true) :
    denoteAInstrs (c.limit + 1 + c.tab) 0 initialAState (msInit c)
      = some (msEntryA c) := by
  exact denoteAInstrs_eq_arun _ _ _ _ (msInit_defined c hok)

private theorem msEntry_reg (c : Cfg) (j : Nat) (h1 : j ≠ rT1) (h2 : j ≠ rT2) :
    (msEntryA c).regs j = srun 0 initialState (initMovs c) j := by
  unfold msEntryA
  rw [msInit_eq, arun_append, arun_append,
    stores_regs 0 (logRows c) _ j h1 h2]
  change (arun 0 initialAState (lift (initMovs c))).regs j = _
  rw [arun_lift_regs]
  rfl

private theorem msEntry_regs_lt (c : Cfg) (j : Nat) : (msEntryA c).regs j < M := by
  unfold msEntryA
  rw [msInit_eq, arun_append]
  refine stores_regs_lt 0 (logRows c) _ ?_ j
  intro j'
  change (arun 0 (arun 0 initialAState (lift (initMovs c)))
    [.store rT1 rT2]).regs j' < M
  change (arun 0 initialAState (lift (initMovs c))).regs j' < M
  rw [arun_lift_regs]
  exact srun_regs_lt 0 (initMovs c) initialState (fun _ => M_pos) j'

private theorem msEntry_arr (c : Cfg) (hok : msOK c = true) (i : Nat) :
    (msEntryA c).arr i = arr0 c i := by
  unfold msEntryA
  rw [msInit_eq, arun_append, arun_append,
    stores_arr 0 (logRows c) _ i (logRows_mem_M c hok)]
  change
    (((logRows c).reverse.find? (fun e => decide (e.1 = i))).map
      (fun e => e.2 % M)).getD
        (if i = 1 % M then c.cell1 % M else 0) = arr0 c i
  unfold logRows
  rw [← List.map_reverse, List.find?_map]
  simp only [Function.comp_def, Option.map_map]
  change
    ((c.logs.reverse.find? (fun e => decide (c.limit + 1 + e.1 = i))).map
      (fun e => e.2 % M)).getD
        (if i = 1 % M then c.cell1 % M else 0) = arr0 c i
  rw [Nat.mod_eq_of_lt one_lt_M]
  unfold arr0 logAt
  by_cases hi : c.limit + 1 ≤ i
  · rw [if_pos hi]
    have hi1 : i ≠ 1 := by
      have hn0 := ok_n0 hok
      have hnlim := ok_n0_le hok
      omega
    rw [if_neg hi1]
    cases hfind : c.logs.reverse.find? (fun e => decide (c.limit + 1 + e.1 = i)) with
    | none => simp
    | some e => simp
  · rw [if_neg hi]
    have hfind : c.logs.reverse.find? (fun e => decide (c.limit + 1 + e.1 = i)) = none := by
      apply List.find?_eq_none.mpr
      intro e he
      intro heq
      simp only [decide_eq_true_eq] at heq
      apply hi
      omega
    rw [hfind]
    rfl

/-- **The entry state is `msEntry`**: the carried registers, the packed cell
for `q = 1`, and the 69 log constants. -/
theorem msEntry_obs (c : Cfg) (hok : msOK c = true) :
    toSt (obsR (msEntryA c)) = msEntry c ∧
      (obsR (msEntryA c)).acc = 0 ∧ (obsR (msEntryA c)).sc = 0 := by
  have hbad : (msEntryA c).regs rBad = 0 := by
    rw [msEntry_reg c rBad (by decide) (by decide)]
    rfl
  have hlb : (msEntryA c).regs rLb = (bias + fpDlit) % M := by
    rw [msEntry_reg c rLb (by decide) (by decide)]
    rfl
  have hlam : (msEntryA c).regs rLam = c.seed % M := by
    rw [msEntry_reg c rLam (by decide) (by decide)]
    rfl
  have hidx : (msEntryA c).regs rIdx = 0 := by
    rw [msEntry_reg c rIdx (by decide) (by decide)]
    rfl
  have hbs : (msEntryA c).regs rBs = 64 := by
    rw [msEntry_reg c rBs (by decide) (by decide)]
    rfl
  have hmx : (msEntryA c).regs rMax = 0 := by
    rw [msEntry_reg c rMax (by decide) (by decide)]
    rfl
  have hcell : (msEntryA c).regs rCell = c.cell1 % M := by
    rw [msEntry_reg c rCell (by decide) (by decide)]
    rfl
  have hacc : (msEntryA c).regs rAcc = 0 := by
    rw [msEntry_reg c rAcc (by decide) (by decide)]
    rfl
  have hsc : (msEntryA c).regs rS = 0 := by
    rw [msEntry_reg c rS (by decide) (by decide)]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · apply St.ext
    · exact hbad
    · exact hlb
    · exact hlam
    · exact hidx
    · exact hbs
    · exact hmx
    · exact hcell
    · funext i
      exact msEntry_arr c hok i
  · exact hacc
  · exact hsc

private theorem arr0_lt (c : Cfg) (i : Nat) : arr0 c i < M := by
  unfold arr0
  split
  · unfold logAt
    exact Nat.mod_lt _ M_pos
  · split
    · exact Nat.mod_lt _ M_pos
    · exact M_pos

theorem msEntry_inv (c : Cfg) (hok : msOK c = true) :
    MSInv c (msEntryA c) ∧ BInv c (obsR (msEntryA c)) := by
  have hregs : ∀ j, (msEntryA c).regs j < M := msEntry_regs_lt c
  have harr : ∀ i, (msEntryA c).arr i < M := by
    intro i
    rw [msEntry_arr c hok i]
    exact arr0_lt c i
  have he := msEntry_obs c hok
  have hidxEq := congrArg St.idx he.1
  have hidx : (msEntryA c).regs rIdx < c.tab := by
    calc
      (msEntryA c).regs rIdx = (msEntry c).idx := hidxEq
      _ = 0 := rfl
      _ < c.tab := ok_tab0 hok
  have hscan : (msEntryA c).regs rS = 0 ∨ 2 ≤ (msEntryA c).regs rS :=
    Or.inl he.2.2
  refine ⟨⟨hregs, harr, hidx, hscan⟩, ?_⟩
  exact ⟨hregs rBad, hregs rLb, hregs rLam, hidx, hregs rBs,
    hregs rMax, hregs rCell, hregs rAcc, hregs rS, hregs rMuQ, harr, hscan⟩

/-! ## The whole loop, folded -/

private def msBlocks (c : Cfg) (F : Nat) : RSt :=
  (List.range F).foldl (block c.B (fun x r => msRound c r x))
    (obsR (msEntryA c))

private def msStates (c : Cfg) (F : Nat) : St :=
  (List.range F).foldl (fun st q => msStep c (c.n0 + q) st) (msEntry c)

private theorem msBlocks_succ (c : Cfg) (F : Nat) :
    msBlocks c (F + 1) =
      block c.B (fun x r => msRound c r x) (msBlocks c F) F := by
  unfold msBlocks
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem msStates_succ (c : Cfg) (F : Nat) :
    msStates c (F + 1) = msStep c (c.n0 + F) (msStates c F) := by
  unfold msStates
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem msBlocks_eq (c : Cfg) (hok : msOK c = true) :
    ∀ F, F ≤ c.len →
      BInv c (msBlocks c F) ∧ toSt (msBlocks c F) = msStates c F := by
  intro F
  induction F with
  | zero =>
      intro _
      exact ⟨(msEntry_inv c hok).2, (msEntry_obs c hok).1⟩
  | succ F ih =>
      intro hF
      have hq : F < c.len := by omega
      obtain ⟨hinv, heq⟩ := ih (by omega)
      rw [msBlocks_succ, msStates_succ]
      refine ⟨?_, ?_⟩
      · rw [block_eq_shift]
        exact prefix_inv c hok F c.B hq (Nat.le_refl _) (msBlocks c F) hinv
      · rw [block_eq_msStep c hok F hq (msBlocks c F) hinv, heq]

/-- **The flat round fold is the reference.**  `BlockedFold.foldl_range_mul`
re-associates the `len · B` applications into `len` blocks; `block_eq_msStep`
identifies one block.  No fold is evaluated. -/
theorem foldl_msRound_eq_msRef (c : Cfg) (hok : msOK c = true) :
    ((List.range (c.len * c.B)).foldl (fun x r => msRound c r x)
      (obsR (msEntryA c))).bad = msRef c := by
  rw [foldl_range_mul c.len c.B (fun x r => msRound c r x)]
  change (msBlocks c c.len).bad = msRef c
  unfold msRef
  change (toSt (msBlocks c c.len)).bad = (msStates c c.len).bad
  exact congrArg St.bad (msBlocks_eq c hok c.len (Nat.le_refl _)).2

/-! ## The encoding obligation, discharged -/

/-- **The program denotes the candidate-level reference.** -/
theorem msProgram_denote (c : Cfg) (hok : msOK c = true) :
    (msProgram c).denote = some (msRef c) := by
  have hstep : ∀ (index : Nat) (s : AState), index < c.len * c.B → MSInv c s →
      denoteAInstrs (c.limit + 1 + c.tab) index s (msBody c) =
        some (arun index s (msBody c)) := by
    intro index s hidx hinv
    exact denoteAInstrs_eq_arun _ _ _ _ (msBody_defined c hok index hidx s hinv)
  have hclosed : ∀ (index : Nat) (s : AState), index < c.len * c.B → MSInv c s →
      MSInv c (arun index s (msBody c)) := by
    intro index s hidx hinv
    exact msBody_inv c hok index hidx s hinv
  have hobs : ∀ (index : Nat) (s : AState), index < c.len * c.B → MSInv c s →
      obsR (arun index s (msBody c)) = msRound c index (obsR s) := by
    intro index s hidx hinv
    exact msBody_obs c hok index hidx s hinv
  have hentry : MSInv c (msEntryA c) := (msEntry_inv c hok).1
  have hres := AProgram.denote_eq_obs_foldl_mem (msProgram c) (MSInv c)
    (fun index s => arun index s (msBody c)) obsR
    (fun index a => msRound c index a) (fun a => a.bad) (msEntryA c)
    (msInit_reaches c hok) hentry hstep hclosed hobs (fun _ _ => rfl)
  have hlc : (msProgram c).loopCount = c.len * c.B := rfl
  rw [hres, hlc, foldl_msRound_eq_msRef c hok]

/-- **`MSEncoding`, proved.** -/
theorem msEncoding (c : Cfg) : MSEncoding c := fun hok => msProgram_denote c hok

end LeanCompCert.Ports.RamareMStar140M

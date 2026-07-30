import LeanCompCert.Verified.Montgomery
import LeanCompCert.Verified.MulWide
import LeanCompCert.Verified.Reflect

/-!
# Two-limb Montgomery arithmetic in the 64-bit instruction set

`Verified/Montgomery.lean` proves the algebra over `Nat`.  This module
realizes it at two limbs using **only** operations the proved fragment has:
`+`, `-`, `*`, `&`, `|`, `<<`, `>>`, and the proved `<` comparison — all
modulo `2⁶⁴`.  There is **no `udiv` and no `urem` anywhere in this file's
machine forms**, which is the whole reason Montgomery was chosen over
Barrett: the fragment's only division is 64 ÷ 64 → 64, and a 128 ÷ 64
division is exactly what it cannot express.

The style throughout is a pair of definitions plus an equality:

* a *mathematical* form written with `/ 2⁶⁴` and `% 2⁶⁴`, about which the
  value theorems are easy; and
* a *machine* form written with word operations only, proved equal to it.

`hl` (the 128-bit product) is imported from `Verified/MulWide.lean`; its
machine form `hlW` replaces that module's `/ 2³²` and `% 2³²` by a shift
and a mask, so the emitted C contains no division at all.

The end of the chain is `montMul2_spec`: the two-limb machine function
computes `Montgomery.montMul 2`, hence (through `Montgomery.montMul_spec`)
a genuine modular product of ~128-bit residues.
-/

namespace LeanCompCert.Verified.Mont2

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.Montgomery (B MontMultiplier redcStep redcIter montMul)

/-- The word modulus, as a numeral. -/
theorem M_val : M = 18446744073709551616 := by decide +kernel

theorem M_eq_B : M = B := rfl

theorem M_pos : 0 < M := by decide +kernel

/-! ## Word operations

Each of these is exactly one `Reflect.Op`, unwrapped from the `Option` its
denotation carries.  Every one is total.
-/

def wadd (x y : Nat) : Nat := (x + y) % M
def wsub (x y : Nat) : Nat := (x + (M - y)) % M
def wmul (x y : Nat) : Nat := (x * y) % M
def wand (x y : Nat) : Nat := (x &&& y) % M
def wshl (x y : Nat) : Nat := (x <<< y) % M
def wshr (x y : Nat) : Nat := (x >>> y) % M
def wlt (x y : Nat) : Nat := if x < y then 1 else 0

theorem wadd_lt (x y : Nat) : wadd x y < M := Nat.mod_lt _ M_pos
theorem wsub_lt (x y : Nat) : wsub x y < M := Nat.mod_lt _ M_pos
theorem wmul_lt (x y : Nat) : wmul x y < M := Nat.mod_lt _ M_pos
theorem wand_lt (x y : Nat) : wand x y < M := Nat.mod_lt _ M_pos
theorem wshl_lt (x y : Nat) : wshl x y < M := Nat.mod_lt _ M_pos
theorem wshr_lt (x y : Nat) : wshr x y < M := Nat.mod_lt _ M_pos
theorem wlt_le_one (x y : Nat) : wlt x y ≤ 1 := by unfold wlt; split <;> omega

/-- Branchless select: `wsel c a b` is `a` when `c = 1` and `b` when
`c = 0`.  Multiplication by a 0/1 flag, so no branch is needed. -/
def wsel (c a b : Nat) : Nat := wadd (wmul a c) (wmul b (wsub 1 c))

theorem wsel_one (a b : Nat) (ha : a < M) : wsel 1 a b = a := by
  have h1 : wsub 1 1 = 0 := by decide +kernel
  show wadd (wmul a 1) (wmul b (wsub 1 1)) = a
  rw [h1]
  simp only [wadd, wmul, M_val] at ha ⊢
  omega

theorem wsel_zero (a b : Nat) (hb : b < M) : wsel 0 a b = b := by
  have h1 : wsub 1 0 = 1 := by decide +kernel
  show wadd (wmul a 0) (wmul b (wsub 1 0)) = b
  rw [h1]
  simp only [wadd, wmul, M_val] at hb ⊢
  omega

/-! ## Add with carry -/

/-- Add with carry, mathematical form. -/
def addc (x y c : Nat) : Nat × Nat := ((x + y + c) % M, (x + y + c) / M)

/-- Add with carry, machine form: two adds and two proved comparisons. -/
def addcW (x y c : Nat) : Nat × Nat :=
  let s := wadd x y
  let t := wadd s c
  (t, wadd (wlt s x) (wlt t s))

theorem addcW_eq (x y c : Nat) (hx : x < M) (hy : y < M) (hc : c ≤ 1) :
    addcW x y c = addc x y c := by
  simp only [addcW, addc, wadd, wlt, M_val, Prod.mk.injEq] at hx hy ⊢
  refine ⟨by omega, ?_⟩
  split <;> split <;> omega

theorem addc_fst_lt (x y c : Nat) : (addc x y c).1 < M := Nat.mod_lt _ M_pos

theorem addc_snd_le (x y c : Nat) (hx : x < M) (hy : y < M) (hc : c ≤ 1) :
    (addc x y c).2 ≤ 1 := by
  simp only [addc, M_val] at hx hy ⊢
  omega

theorem addc_spec (x y c : Nat) :
    (addc x y c).1 + M * (addc x y c).2 = x + y + c := by
  simp only [addc, M_val]
  omega

/-! ## Subtract with borrow -/

/-- Subtract with borrow, mathematical form. -/
def sbbc (x y c : Nat) : Nat × Nat :=
  if x < y + c then (x + M - y - c, 1) else (x - y - c, 0)

/-- Subtract with borrow, machine form. -/
def sbbcW (x y c : Nat) : Nat × Nat :=
  let t := wsub x y
  let s := wsub t c
  (s, wadd (wlt x y) (wlt t c))

theorem sbbcW_eq (x y c : Nat) (hx : x < M) (hy : y < M) (hc : c ≤ 1) :
    sbbcW x y c = sbbc x y c := by
  simp only [sbbcW, sbbc, wsub, wadd, wlt, M_val] at hx hy ⊢
  by_cases h : x < y + c
  · rw [if_pos h, Prod.mk.injEq]
    refine ⟨by omega, ?_⟩
    split <;> split <;> omega
  · rw [if_neg h, Prod.mk.injEq]
    refine ⟨by omega, ?_⟩
    split <;> split <;> omega

theorem sbbc_spec (x y c : Nat) (hx : x < M) (hy : y < M) (hc : c ≤ 1) :
    (sbbc x y c).1 + y + c = x + M * (sbbc x y c).2 ∧
      (sbbc x y c).1 < M ∧ (sbbc x y c).2 ≤ 1 := by
  simp only [sbbc, M_val] at hx hy ⊢
  by_cases h : x < y + c
  · rw [if_pos h]
    refine ⟨by omega, by omega, by omega⟩
  · rw [if_neg h]
    refine ⟨by omega, by omega, by omega⟩

/-! ## The 128-bit product without division -/

/-- `MulWide.hl` with the half-limb split done by a shift and a mask
instead of `/ 2³²` and `% 2³²`.  This is the only place the emitted code
could have contained a division, and it does not. -/
def hlW (a b : Nat) : Nat × Nat :=
  let a0 := wand a 4294967295
  let a1 := wshr a 32
  let b0 := wand b 4294967295
  let b1 := wshr b 32
  let p00 := wmul a0 b0
  let p01 := wmul a0 b1
  let p10 := wmul a1 b0
  let p11 := wmul a1 b1
  let mid := wadd p01 p10
  let carryMid := wlt mid p01
  let lo := wadd p00 (wshl mid 32)
  let carryLo := wlt lo p00
  let hi := wadd (wadd (wadd p11 (wshr mid 32)) (wshl carryMid 32)) carryLo
  (lo, hi)

/-- `2³²` as a numeral, so that `omega` can see it. -/
private theorem two_pow_32 : (2 : Nat) ^ 32 = 4294967296 := by decide +kernel

/-- `M` is `MulWide.B64`. -/
private theorem MB64 : M = MulWide.B64 := M_val

/-- Masking with `2³² − 1` is reduction modulo `2³²`. -/
private theorem wand_mask (a : Nat) : wand a 4294967295 = a % 4294967296 := by
  show (a &&& 4294967295) % M = a % 4294967296
  have e : (4294967295 : Nat) = 2 ^ 32 - 1 := by decide +kernel
  rw [e, Nat.and_two_pow_sub_one_eq_mod, two_pow_32]
  refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide +kernel)) ?_)
  rw [M_val]; omega

/-- A right shift of a word is a division by a power of two. -/
private theorem wshr_eq (x n : Nat) (hx : x < M) : wshr x n = x / 2 ^ n := by
  show (x >>> n) % M = x / 2 ^ n
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)

/-- A product of half-limbs does not overflow. -/
private theorem wmul_half (u v : Nat) (hu : u < 4294967296) (hv : v < 4294967296) :
    wmul u v = u * v := by
  show (u * v) % M = u * v
  refine Nat.mod_eq_of_lt ?_
  have h := Nat.mul_lt_mul_of_lt_of_lt hu hv
  rw [M_val]; omega

theorem hlW_eq (a b : Nat) (ha : a < M) (hb : b < M) :
    hlW a b = MulWide.hl a b := by
  have ha' : a < 18446744073709551616 := M_val ▸ ha
  have hb' : b < 18446744073709551616 := M_val ▸ hb
  have ha0 : a % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide +kernel)
  have hb0 : b % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide +kernel)
  have ha1 : a / 2 ^ 32 < 4294967296 := by rw [two_pow_32]; omega
  have hb1 : b / 2 ^ 32 < 4294967296 := by rw [two_pow_32]; omega
  have hhi := MulWide.hl_hi_lt a b (MB64 ▸ ha) (MB64 ▸ hb)
  simp only [hlW]
  rw [wand_mask a, wand_mask b, wshr_eq a 32 ha, wshr_eq b 32 hb,
    wmul_half _ _ ha0 hb0, wmul_half _ _ ha0 hb1, wmul_half _ _ ha1 hb0,
    wmul_half _ _ ha1 hb1, wshr_eq _ 32 (wadd_lt _ _)]
  simp only [MulWide.hl, MulWide.B32, MulWide.B64, wadd, wlt, wshl,
    Nat.shiftLeft_eq, two_pow_32, M_val, Prod.mk.injEq, true_and] at hhi ⊢
  revert hhi
  split <;> split <;> omega

/-- The product spec, transported to the machine form. -/
theorem hlW_spec (a b : Nat) (ha : a < M) (hb : b < M) :
    (hlW a b).1 + M * (hlW a b).2 = a * b ∧
      (hlW a b).1 < M ∧ (hlW a b).2 < M := by
  have h := MulWide.hl_spec a b (MB64 ▸ ha) (MB64 ▸ hb)
  have h2 := MulWide.hl_hi_lt a b (MB64 ▸ ha) (MB64 ▸ hb)
  rw [hlW_eq a b ha hb, MB64]
  exact ⟨h.1, h.2, h2⟩

/-- The high word of a product of words is at most `2⁶⁴ − 2`, so adding a
carry to it cannot overflow. -/
theorem hlW_hi_le (a b : Nat) (ha : a < M) (hb : b < M) :
    (hlW a b).2 + 1 < M := by
  have h := hlW_spec a b ha hb
  have hM1 : 0 < M - 1 := by rw [M_val]; omega
  cases Nat.lt_or_ge ((hlW a b).2 + 1) M with
  | inl h' => exact h'
  | inr h' =>
      exfalso
      have hge : M - 1 ≤ (hlW a b).2 := by omega
      have h1 : M * (M - 1) ≤ M * (hlW a b).2 := Nat.mul_le_mul_left M hge
      have h2 : a * b ≤ (M - 1) * (M - 1) := Nat.mul_le_mul (by omega) (by omega)
      have h3 : (M - 1) * (M - 1) + (M - 1) = M * (M - 1) := by
        have e : (M - 1) * (M - 1) + 1 * (M - 1) = (M - 1 + 1) * (M - 1) := by
          rw [← Nat.add_mul]
        have hM : M - 1 + 1 = M := by omega
        rw [Nat.one_mul] at e
        rw [e, hM]
      omega

/-! ## Limb values -/

/-- Value of two little-endian limbs. -/
def pval (x0 x1 : Nat) : Nat := x0 + M * x1

/-- Value of four little-endian limbs. -/
def qval (t0 t1 t2 t3 : Nat) : Nat := t0 + M * (t1 + M * (t2 + M * t3))

/-! ## The 2 × 2 → 4 limb product -/

/-- Schoolbook by rows: `a · b₀` then `a · b₁`, then combine.  Every carry
in this shape is a single bit, which keeps the value proof linear. -/
def mul2 (a0 a1 b0 b1 : Nat) : Nat × Nat × Nat × Nat :=
  let x := hlW a0 b0
  let y := hlW a1 b0
  let r1 := addcW x.2 y.1 0
  let r2 := wadd y.2 r1.2
  let u := hlW a0 b1
  let v := hlW a1 b1
  let s1 := addcW u.2 v.1 0
  let s2 := wadd v.2 s1.2
  let p1 := addcW r1.1 u.1 0
  let p2 := addcW r2 s1.1 p1.2
  let p3 := wadd s2 p2.2
  (x.1, p1.1, p2.1, p3)

/-- **The four-limb product is exact.** -/
theorem mul2_val (a0 a1 b0 b1 : Nat)
    (ha0 : a0 < M) (ha1 : a1 < M) (hb0 : b0 < M) (hb1 : b1 < M) :
    qval (mul2 a0 a1 b0 b1).1 (mul2 a0 a1 b0 b1).2.1
        (mul2 a0 a1 b0 b1).2.2.1 (mul2 a0 a1 b0 b1).2.2.2 =
      pval a0 a1 * pval b0 b1 := by
  have hexp : pval a0 a1 * pval b0 b1
      = a0 * b0 + M * (a1 * b0) + M * (a0 * b1) + M * (M * (a1 * b1)) := by
    simp only [pval]
    simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
  have hAlt : pval a0 a1 < M * M := by
    simp only [pval, M_val] at ha0 ha1 ⊢; omega
  have hBlt : pval b0 b1 < M * M := by
    simp only [pval, M_val] at hb0 hb1 ⊢; omega
  have hAB : pval a0 a1 * pval b0 b1 < M * M * (M * M) :=
    Nat.mul_lt_mul_of_lt_of_lt hAlt hBlt
  have hx := hlW_spec a0 b0 ha0 hb0
  have hxle := hlW_hi_le a0 b0 ha0 hb0
  have hy := hlW_spec a1 b0 ha1 hb0
  have hyle := hlW_hi_le a1 b0 ha1 hb0
  have hu := hlW_spec a0 b1 ha0 hb1
  have hule := hlW_hi_le a0 b1 ha0 hb1
  have hv := hlW_spec a1 b1 ha1 hb1
  have hvle := hlW_hi_le a1 b1 ha1 hb1
  simp only [mul2]
  revert hx hxle; generalize hlW a0 b0 = x; intro hx hxle
  revert hy hyle; generalize hlW a1 b0 = y; intro hy hyle
  revert hu hule; generalize hlW a0 b1 = u; intro hu hule
  revert hv hvle; generalize hlW a1 b1 = v; intro hv hvle
  rw [addcW_eq x.2 y.1 0 hx.2.2 hy.2.1 (by omega)]
  have hr1 := addc_spec x.2 y.1 0
  have hr1a := addc_fst_lt x.2 y.1 0
  have hr1b := addc_snd_le x.2 y.1 0 hx.2.2 hy.2.1 (by omega)
  revert hr1 hr1a hr1b; generalize addc x.2 y.1 0 = r1; intro hr1 hr1a hr1b
  have hr2 : wadd y.2 r1.2 = y.2 + r1.2 := Nat.mod_eq_of_lt (by omega)
  rw [hr2]
  rw [addcW_eq u.2 v.1 0 hu.2.2 hv.2.1 (by omega)]
  have hs1 := addc_spec u.2 v.1 0
  have hs1a := addc_fst_lt u.2 v.1 0
  have hs1b := addc_snd_le u.2 v.1 0 hu.2.2 hv.2.1 (by omega)
  revert hs1 hs1a hs1b; generalize addc u.2 v.1 0 = s1; intro hs1 hs1a hs1b
  have hs2 : wadd v.2 s1.2 = v.2 + s1.2 := Nat.mod_eq_of_lt (by omega)
  rw [hs2]
  rw [addcW_eq r1.1 u.1 0 hr1a hu.2.1 (by omega)]
  have hp1 := addc_spec r1.1 u.1 0
  have hp1a := addc_fst_lt r1.1 u.1 0
  have hp1b := addc_snd_le r1.1 u.1 0 hr1a hu.2.1 (by omega)
  revert hp1 hp1a hp1b; generalize addc r1.1 u.1 0 = p1; intro hp1 hp1a hp1b
  rw [addcW_eq (y.2 + r1.2) s1.1 p1.2 (by omega) hs1a hp1b]
  have hp2 := addc_spec (y.2 + r1.2) s1.1 p1.2
  have hp2a := addc_fst_lt (y.2 + r1.2) s1.1 p1.2
  have hp2b := addc_snd_le (y.2 + r1.2) s1.1 p1.2 (by omega) hs1a hp1b
  revert hp2 hp2a hp2b
  generalize addc (y.2 + r1.2) s1.1 p1.2 = p2
  intro hp2 hp2a hp2b
  have hident : qval x.1 p1.1 p2.1 (v.2 + s1.2 + p2.2) = pval a0 a1 * pval b0 b1 := by
    simp only [qval, pval, M_val] at hexp hx hy hu hv hr1 hs1 hp1 hp2 ⊢
    omega
  have hWlt : v.2 + s1.2 + p2.2 < M := by
    simp only [qval, pval, M_val] at hident hAB hx hp1a hp2a ⊢
    omega
  have hp3 : wadd (v.2 + s1.2) p2.2 = v.2 + s1.2 + p2.2 := Nat.mod_eq_of_lt hWlt
  rw [hp3]
  exact hident

theorem mul2_lt (a0 a1 b0 b1 : Nat)
    (ha0 : a0 < M) (ha1 : a1 < M) (hb0 : b0 < M) (hb1 : b1 < M) :
    (mul2 a0 a1 b0 b1).1 < M ∧ (mul2 a0 a1 b0 b1).2.1 < M ∧
      (mul2 a0 a1 b0 b1).2.2.1 < M ∧ (mul2 a0 a1 b0 b1).2.2.2 < M := by
  simp only [mul2, addcW]
  exact ⟨(hlW_spec a0 b0 ha0 hb0).2.1, wadd_lt _ _, wadd_lt _ _, wadd_lt _ _⟩

/-! ## One two-limb Montgomery reduction step -/

/--
One `Montgomery.redcStep` at two limbs: form `m`, add `m · N`, and drop the
low limb.  The low limb is provably zero (`Montgomery.redcStep_mul`), which
is what makes "drop the limb" a legal division.
-/
def redcStep2 (n0 n1 np t0 t1 t2 t3 : Nat) : Nat × Nat × Nat × Nat :=
  let m := wmul t0 np
  let p := hlW m n0
  let q := hlW m n1
  let u := addcW p.2 q.1 0
  let v := wadd q.2 u.2
  let w0 := addcW t0 p.1 0
  let w1 := addcW t1 u.1 w0.2
  let w2 := addcW t2 v w1.2
  let w3 := addcW t3 0 w2.2
  (w1.1, w2.1, w3.1, w3.2)

theorem redcStep2_lt (n0 n1 np t0 t1 t2 t3 : Nat)
    (hn0 : n0 < M) (hn1 : n1 < M) (hnp : np < M)
    (h0 : t0 < M) (h1 : t1 < M) (h2 : t2 < M) (h3 : t3 < M) :
    (redcStep2 n0 n1 np t0 t1 t2 t3).1 < M ∧
      (redcStep2 n0 n1 np t0 t1 t2 t3).2.1 < M ∧
      (redcStep2 n0 n1 np t0 t1 t2 t3).2.2.1 < M ∧
      (redcStep2 n0 n1 np t0 t1 t2 t3).2.2.2 < M := by
  simp only [redcStep2, addcW]
  exact ⟨wadd_lt _ _, wadd_lt _ _, wadd_lt _ _, wadd_lt _ _⟩

/-- **One machine reduction step realizes one `Montgomery.redcStep`.** -/
theorem redcStep2_val (n0 n1 np t0 t1 t2 t3 : Nat)
    (hn0 : n0 < M) (hn1 : n1 < M) (hnp : np < M)
    (h0 : t0 < M) (h1 : t1 < M) (h2 : t2 < M) (h3 : t3 < M)
    (hinv : MontMultiplier (pval n0 n1) np) :
    qval (redcStep2 n0 n1 np t0 t1 t2 t3).1
        (redcStep2 n0 n1 np t0 t1 t2 t3).2.1
        (redcStep2 n0 n1 np t0 t1 t2 t3).2.2.1
        (redcStep2 n0 n1 np t0 t1 t2 t3).2.2.2 =
      redcStep (pval n0 n1) np (qval t0 t1 t2 t3) := by
  have hT0 : qval t0 t1 t2 t3 % M = t0 := by
    show (t0 + M * (t1 + M * (t2 + M * t3))) % M = t0
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  have hredcM : Montgomery.redcM np (qval t0 t1 t2 t3) = wmul t0 np := by
    show (qval t0 t1 t2 t3 % M * np) % M = (t0 * np) % M
    rw [hT0]
  have hstep := Montgomery.redcStep_mul (pval n0 n1) np (qval t0 t1 t2 t3) hinv
  rw [hredcM] at hstep
  have hm : wmul t0 np < M := wmul_lt _ _
  simp only [redcStep2]
  revert hstep hm
  generalize wmul t0 np = m
  intro hstep hm
  have hp := hlW_spec m n0 hm hn0
  have hple := hlW_hi_le m n0 hm hn0
  revert hp hple; generalize hlW m n0 = p; intro hp hple
  have hq := hlW_spec m n1 hm hn1
  have hqle := hlW_hi_le m n1 hm hn1
  revert hq hqle; generalize hlW m n1 = q; intro hq hqle
  rw [addcW_eq p.2 q.1 0 hp.2.2 hq.2.1 (by omega)]
  have hu := addc_spec p.2 q.1 0
  have hua := addc_fst_lt p.2 q.1 0
  have hub := addc_snd_le p.2 q.1 0 hp.2.2 hq.2.1 (by omega)
  revert hu hua hub; generalize addc p.2 q.1 0 = u; intro hu hua hub
  have hvv : wadd q.2 u.2 = q.2 + u.2 := Nat.mod_eq_of_lt (by omega)
  rw [hvv]
  rw [addcW_eq t0 p.1 0 h0 hp.2.1 (by omega)]
  have hw0 := addc_spec t0 p.1 0
  have hw0a := addc_fst_lt t0 p.1 0
  have hw0b := addc_snd_le t0 p.1 0 h0 hp.2.1 (by omega)
  revert hw0 hw0a hw0b; generalize addc t0 p.1 0 = w0; intro hw0 hw0a hw0b
  rw [addcW_eq t1 u.1 w0.2 h1 hua hw0b]
  have hw1 := addc_spec t1 u.1 w0.2
  have hw1a := addc_fst_lt t1 u.1 w0.2
  have hw1b := addc_snd_le t1 u.1 w0.2 h1 hua hw0b
  revert hw1 hw1a hw1b; generalize addc t1 u.1 w0.2 = w1; intro hw1 hw1a hw1b
  rw [addcW_eq t2 (q.2 + u.2) w1.2 h2 (by omega) hw1b]
  have hw2 := addc_spec t2 (q.2 + u.2) w1.2
  have hw2a := addc_fst_lt t2 (q.2 + u.2) w1.2
  have hw2b := addc_snd_le t2 (q.2 + u.2) w1.2 h2 (by omega) hw1b
  revert hw2 hw2a hw2b
  generalize addc t2 (q.2 + u.2) w1.2 = w2
  intro hw2 hw2a hw2b
  rw [addcW_eq t3 0 w2.2 h3 M_pos hw2b]
  have hw3 := addc_spec t3 0 w2.2
  have hw3a := addc_fst_lt t3 0 w2.2
  have hw3b := addc_snd_le t3 0 w2.2 h3 M_pos hw2b
  revert hw3 hw3a hw3b; generalize addc t3 0 w2.2 = w3; intro hw3 hw3a hw3b
  have hmN : m * pval n0 n1 = (p.1 + M * p.2) + M * (q.1 + M * q.2) := by
    rw [hp.1, hq.1]
    show m * (n0 + M * n1) = m * n0 + M * (m * n1)
    rw [Nat.mul_add, Nat.mul_left_comm]
  have hBv : Montgomery.B = 18446744073709551616 := M_val
  simp only [qval, pval, M_val, hBv] at hstep hmN hw0 hw1 hw2 hw3 hu hw0a ⊢
  omega

/-! ## Conditional subtraction -/

/-- `sub2 n0 n1 x0 x1` is `(x − N, borrow)` at two limbs. -/
def sub2 (n0 n1 x0 x1 : Nat) : Nat × Nat × Nat :=
  let d0 := sbbcW x0 n0 0
  let d1 := sbbcW x1 n1 d0.2
  (d0.1, d1.1, d1.2)

/-- Branchless `if x ≥ N then x − N else x`. -/
def condSub2 (n0 n1 x0 x1 : Nat) : Nat × Nat :=
  let d := sub2 n0 n1 x0 x1
  let ge := wsub 1 d.2.2
  (wsel ge d.1 x0, wsel ge d.2.1 x1)

theorem condSub2_val (n0 n1 x0 x1 : Nat)
    (hn0 : n0 < M) (hn1 : n1 < M) (hx0 : x0 < M) (hx1 : x1 < M) :
    pval (condSub2 n0 n1 x0 x1).1 (condSub2 n0 n1 x0 x1).2 =
        (if pval x0 x1 < pval n0 n1 then pval x0 x1
         else pval x0 x1 - pval n0 n1) ∧
      (condSub2 n0 n1 x0 x1).1 < M ∧ (condSub2 n0 n1 x0 x1).2 < M := by
  simp only [condSub2, sub2]
  rw [sbbcW_eq x0 n0 0 hx0 hn0 (by omega)]
  have hd0 := sbbc_spec x0 n0 0 hx0 hn0 (by omega)
  revert hd0; generalize sbbc x0 n0 0 = d0; intro hd0
  rw [sbbcW_eq x1 n1 d0.2 hx1 hn1 hd0.2.2]
  have hd1 := sbbc_spec x1 n1 d0.2 hx1 hn1 hd0.2.2
  revert hd1; generalize sbbc x1 n1 d0.2 = d1; intro hd1
  have hcase : d1.2 = 0 ∨ d1.2 = 1 := by omega
  cases hcase with
  | inl h =>
      rw [h]
      have hge : wsub 1 0 = 1 := by decide +kernel
      rw [hge, wsel_one d0.1 x0 hd0.2.1, wsel_one d1.1 x1 hd1.2.1]
      have hnot : ¬ (pval x0 x1 < pval n0 n1) := by
        simp only [pval, M_val] at *; omega
      rw [if_neg hnot]
      refine ⟨?_, hd0.2.1, hd1.2.1⟩
      simp only [pval, M_val] at *; omega
  | inr h =>
      rw [h]
      have hge : wsub 1 1 = 0 := by decide +kernel
      rw [hge, wsel_zero d0.1 x0 hx0, wsel_zero d1.1 x1 hx1]
      have hlt : pval x0 x1 < pval n0 n1 := by
        simp only [pval, M_val] at *; omega
      rw [if_pos hlt]
      exact ⟨rfl, hx0, hx1⟩

/-! ## Two-limb Montgomery multiplication -/

/-- **The deliverable**: a modular multiplication of ~128-bit residues in
the 64-bit instruction set, with no division anywhere. -/
def montMul2 (n0 n1 np a0 a1 b0 b1 : Nat) : Nat × Nat :=
  let p := mul2 a0 a1 b0 b1
  let r := redcStep2 n0 n1 np p.1 p.2.1 p.2.2.1 p.2.2.2
  let r2 := redcStep2 n0 n1 np r.1 r.2.1 r.2.2.1 r.2.2.2
  condSub2 n0 n1 r2.1 r2.2.1

/-- Two limbs below `2⁶⁴` whose value is below `2¹²⁸` really are the value. -/
theorem qval_of_lt (t0 t1 t2 t3 : Nat)
    (h0 : t0 < M) (h1 : t1 < M) (h2 : t2 < M) (h3 : t3 < M)
    (hlt : qval t0 t1 t2 t3 < M * M) :
    t2 = 0 ∧ t3 = 0 ∧ qval t0 t1 t2 t3 = pval t0 t1 := by
  simp only [qval, pval, M_val] at h0 h1 hlt ⊢
  omega

/--
**The two-limb Montgomery multiplication spec** — the machine function
computes `Montgomery.montMul 2`, hence (with `Montgomery.montMul_spec`) a
true modular product.
-/
theorem montMul2_val (n0 n1 np a0 a1 b0 b1 : Nat)
    (hn0 : n0 < M) (hn1 : n1 < M) (hnp : np < M)
    (ha0 : a0 < M) (ha1 : a1 < M) (hb0 : b0 < M) (hb1 : b1 < M)
    (hodd : pval n0 n1 % 2 = 1) (hN : 0 < pval n0 n1)
    (hHalf : 2 * pval n0 n1 ≤ M * M)
    (hinv : MontMultiplier (pval n0 n1) np)
    (ha : pval a0 a1 < pval n0 n1) (hb : pval b0 b1 < pval n0 n1) :
    pval (montMul2 n0 n1 np a0 a1 b0 b1).1 (montMul2 n0 n1 np a0 a1 b0 b1).2 =
        montMul 2 (pval n0 n1) np (pval a0 a1) (pval b0 b1) ∧
      (montMul2 n0 n1 np a0 a1 b0 b1).1 < M ∧
      (montMul2 n0 n1 np a0 a1 b0 b1).2 < M := by
  have hB2 : Montgomery.B ^ 2 = M * M := by rw [Nat.pow_two, ← M_eq_B]
  have hNB : pval n0 n1 ≤ Montgomery.B ^ 2 := by rw [hB2]; omega
  have hABlt : pval a0 a1 * pval b0 b1
      < pval n0 n1 * Montgomery.B ^ 2 + pval n0 n1 := by
    have h1 : pval a0 a1 * pval b0 b1 < pval n0 n1 * pval n0 n1 :=
      Nat.mul_lt_mul_of_lt_of_lt ha hb
    have h2 : pval n0 n1 * pval n0 n1 ≤ pval n0 n1 * Montgomery.B ^ 2 :=
      Nat.mul_le_mul_left _ hNB
    omega
  have htlt : Montgomery.redcIter 2 (pval n0 n1) np (pval a0 a1 * pval b0 b1)
      < pval n0 n1 + pval n0 n1 :=
    Montgomery.redcIter_lt (pval n0 n1) np hinv 2 _ hABlt
  have hiter : Montgomery.redcIter 2 (pval n0 n1) np (pval a0 a1 * pval b0 b1)
      = redcStep (pval n0 n1) np
          (redcStep (pval n0 n1) np (pval a0 a1 * pval b0 b1)) := rfl
  simp only [montMul2]
  have hp := mul2_val a0 a1 b0 b1 ha0 ha1 hb0 hb1
  have hplt := mul2_lt a0 a1 b0 b1 ha0 ha1 hb0 hb1
  revert hp hplt; generalize mul2 a0 a1 b0 b1 = p; intro hp hplt
  have hr := redcStep2_val n0 n1 np p.1 p.2.1 p.2.2.1 p.2.2.2 hn0 hn1 hnp
    hplt.1 hplt.2.1 hplt.2.2.1 hplt.2.2.2 hinv
  have hrlt := redcStep2_lt n0 n1 np p.1 p.2.1 p.2.2.1 p.2.2.2 hn0 hn1 hnp
    hplt.1 hplt.2.1 hplt.2.2.1 hplt.2.2.2
  rw [hp] at hr
  revert hr hrlt
  generalize redcStep2 n0 n1 np p.1 p.2.1 p.2.2.1 p.2.2.2 = r
  intro hr hrlt
  have hr2 := redcStep2_val n0 n1 np r.1 r.2.1 r.2.2.1 r.2.2.2 hn0 hn1 hnp
    hrlt.1 hrlt.2.1 hrlt.2.2.1 hrlt.2.2.2 hinv
  have hr2lt := redcStep2_lt n0 n1 np r.1 r.2.1 r.2.2.1 r.2.2.2 hn0 hn1 hnp
    hrlt.1 hrlt.2.1 hrlt.2.2.1 hrlt.2.2.2
  rw [hr, ← hiter] at hr2
  revert hr2 hr2lt
  generalize redcStep2 n0 n1 np r.1 r.2.1 r.2.2.1 r.2.2.2 = r2
  intro hr2 hr2lt
  have hqv := qval_of_lt r2.1 r2.2.1 r2.2.2.1 r2.2.2.2 hr2lt.1 hr2lt.2.1
    hr2lt.2.2.1 hr2lt.2.2.2 (by rw [hr2]; omega)
  have hpv : pval r2.1 r2.2.1
      = Montgomery.redcIter 2 (pval n0 n1) np (pval a0 a1 * pval b0 b1) := by
    rw [← hqv.2.2]; exact hr2
  have hcs := condSub2_val n0 n1 r2.1 r2.2.1 hn0 hn1 hr2lt.1 hr2lt.2.1
  refine ⟨?_, hcs.2.1, hcs.2.2⟩
  rw [hcs.1, hpv]
  simp only [Montgomery.montMul]

/-! ## Doubling modulo `N`

Entering the Montgomery domain needs `x · 2ᵏ mod N`, and that too must be
computed without division.  Repeated doubling with a conditional subtract
does it in `k` steps of pure word arithmetic.
-/

/-- `2x mod N` at two limbs, for `x < N` and `2N ≤ 2¹²⁸`. -/
def dbl2 (n0 n1 x0 x1 : Nat) : Nat × Nat :=
  let c := wshr x0 63
  let d0 := wshl x0 1
  let d1 := wadd (wshl x1 1) c
  condSub2 n0 n1 d0 d1

theorem dbl2_val (n0 n1 x0 x1 : Nat)
    (hn0 : n0 < M) (hn1 : n1 < M) (hx0 : x0 < M) (hx1 : x1 < M)
    (hHalf : 2 * pval n0 n1 ≤ M * M)
    (hx : pval x0 x1 < pval n0 n1) :
    pval (dbl2 n0 n1 x0 x1).1 (dbl2 n0 n1 x0 x1).2 =
        2 * pval x0 x1 % pval n0 n1 ∧
      (dbl2 n0 n1 x0 x1).1 < M ∧ (dbl2 n0 n1 x0 x1).2 < M ∧
      pval (dbl2 n0 n1 x0 x1).1 (dbl2 n0 n1 x0 x1).2 < pval n0 n1 := by
  have hNpos : 0 < pval n0 n1 := by omega
  have h2x : 2 * pval x0 x1 < M * M := by
    simp only [pval, M_val] at hx hHalf ⊢; omega
  have hc : wshr x0 63 = x0 / 9223372036854775808 := by
    have e : (2 : Nat) ^ 63 = 9223372036854775808 := by decide +kernel
    rw [wshr_eq x0 63 hx0, e]
  have hd0 : wshl x0 1 = (x0 * 2) % M := by
    simp only [wshl, Nat.shiftLeft_eq, Nat.pow_one]
  have hd1 : wshl x1 1 = (x1 * 2) % M := by
    simp only [wshl, Nat.shiftLeft_eq, Nat.pow_one]
  simp only [dbl2]
  rw [hc, hd0, hd1]
  have hkey : pval ((x0 * 2) % M) (wadd ((x1 * 2) % M) (x0 / 9223372036854775808))
      = 2 * pval x0 x1 := by
    simp only [pval, wadd, M_val] at hx0 hx1 h2x ⊢
    omega
  have hcs := condSub2_val n0 n1 ((x0 * 2) % M)
    (wadd ((x1 * 2) % M) (x0 / 9223372036854775808)) hn0 hn1
    (Nat.mod_lt _ M_pos) (wadd_lt _ _)
  have hmain : pval (condSub2 n0 n1 ((x0 * 2) % M)
        (wadd ((x1 * 2) % M) (x0 / 9223372036854775808))).1
      (condSub2 n0 n1 ((x0 * 2) % M)
        (wadd ((x1 * 2) % M) (x0 / 9223372036854775808))).2
      = 2 * pval x0 x1 % pval n0 n1 := by
    rw [hcs.1, hkey]
    by_cases hlt : 2 * pval x0 x1 < pval n0 n1
    · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
    · rw [if_neg hlt]
      have hge : pval n0 n1 ≤ 2 * pval x0 x1 := Nat.not_lt.mp hlt
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hmain, hcs.2.1, hcs.2.2, ?_⟩
  rw [hmain]
  exact Nat.mod_lt _ hNpos

/-- Reducing before scaling by a power of two is harmless. -/
private theorem mod_mul_pow (N x k : Nat) :
    (x % N * 2 ^ k) % N = (x * 2 ^ k) % N := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- `k` doublings: `x · 2ᵏ mod N`. -/
def dblIter (n0 n1 : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, x0, x1 => (x0, x1)
  | k + 1, x0, x1 => dblIter n0 n1 k (dbl2 n0 n1 x0 x1).1 (dbl2 n0 n1 x0 x1).2

theorem dblIter_val (n0 n1 : Nat)
    (hn0 : n0 < M) (hn1 : n1 < M)
    (hHalf : 2 * pval n0 n1 ≤ M * M) :
    ∀ (k x0 x1 : Nat), x0 < M → x1 < M → pval x0 x1 < pval n0 n1 →
      pval (dblIter n0 n1 k x0 x1).1 (dblIter n0 n1 k x0 x1).2 =
          pval x0 x1 * 2 ^ k % pval n0 n1 ∧
        (dblIter n0 n1 k x0 x1).1 < M ∧ (dblIter n0 n1 k x0 x1).2 < M ∧
        pval (dblIter n0 n1 k x0 x1).1 (dblIter n0 n1 k x0 x1).2 <
          pval n0 n1 := by
  intro k
  induction k with
  | zero =>
      intro x0 x1 hx0 hx1 hx
      simp only [dblIter]
      refine ⟨?_, hx0, hx1, hx⟩
      rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx]
  | succ k ih =>
      intro x0 x1 hx0 hx1 hx
      have hd := dbl2_val n0 n1 x0 x1 hn0 hn1 hx0 hx1 hHalf hx
      have hrec := ih (dbl2 n0 n1 x0 x1).1 (dbl2 n0 n1 x0 x1).2
        hd.2.1 hd.2.2.1 hd.2.2.2
      simp only [dblIter]
      refine ⟨?_, hrec.2.1, hrec.2.2.1, hrec.2.2.2⟩
      rw [hrec.1, hd.1, mod_mul_pow]
      have e : 2 * pval x0 x1 * 2 ^ k = pval x0 x1 * 2 ^ (k + 1) := by
        rw [Nat.pow_succ]
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [e]

end LeanCompCert.Verified.Mont2

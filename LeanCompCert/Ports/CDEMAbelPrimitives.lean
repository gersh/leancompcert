import LeanCompCert.Ports.AddWidePort
import LeanCompCert.Ports.Section413G1Denote

/-!
# Scalar arithmetic used by the CDEM Abel scan

`CDEMAbelScan` emits three branchless scalar combinators inside its array
program: a conditional select, a 64-by-64 to 128-bit product, and a two-limb
addition.  The arithmetic proofs already existed in the generic wide-word
library and in the Section 4.13 denotation development, but the CDEM scan had
no theorem stated against its own instruction lists.

This file supplies that missing machine-to-model layer.  Each theorem below
is about `arun` of the literal block used by `CDEMAbelScan`; in particular the
array-frame conjunct records that these arithmetic stages cannot silently
change the sieve plane.  The product theorem is exact over `Nat`, and the
addition theorem is exact modulo `2^128`, with a no-wrap corollary for the
accumulator invariant.
-/

namespace LeanCompCert.Ports.CDEMAbelPrimitives

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports

/-! ## Branchless selection -/

/-- The actual CDEM selector returns `x` at gate one and `y` at gate zero,
and cannot modify the array. -/
theorem muxBody_arun (k : Nat) (st : AState) (dst gate x y sc : Nat)
    (hd : sc ≠ dst) (hgt : sc ≠ gate) (hx : sc ≠ x) (hy : sc ≠ y)
    (hg : st.regs gate ≤ 1) (hword : ∀ j, st.regs j < M) :
    let out := arun k st (CDEMAbelScan.muxBody dst gate x y sc)
    out.regs dst = (if st.regs gate = 1 then st.regs x else st.regs y) ∧
      out.arr = st.arr := by
  rw [Section413G1Denote.muxBody_lift, arun_lift]
  exact ⟨Section413G1Denote.muxS_spec k st.regs dst gate x y sc
    hd hgt hx hy hg hword, rfl⟩

/-! ## Wide multiplication -/

/-- The CDEM half-limb multiplier returns the library's proved limb pair and
does not modify the array. -/
theorem mulWideBody_arun_limbs (k : Nat) (st : AState)
    (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Section413G1Denote.Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : Section413G1Denote.NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : Section413G1Denote.NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : Section413G1Denote.NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : Section413G1Denote.NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hword : ∀ j, st.regs j < M) :
    let out := arun k st
      (CDEMAbelScan.mulWideBody ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (out.regs rlo, out.regs rhi) = MulWide.hl (st.regs ra) (st.regs rb) ∧
      out.arr = st.arr := by
  rw [Section413G1Denote.mulWideBody_lift, arun_lift]
  have h := Section413G1Denote.mulWideG_hl k st.regs ra rb rlo rhi
    s0 s1 s2 s3 s4 s5 s6 s7 hD hra hrb hrlo hrhi hlohi hword
  exact ⟨Prod.ext h.1 h.2, rfl⟩

/-- Consequently, the two output registers of the literal CDEM block
recombine to the exact 128-bit product of its input registers. -/
theorem mulWideBody_arun_exact (k : Nat) (st : AState)
    (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hD : Section413G1Denote.Distinct8 s0 s1 s2 s3 s4 s5 s6 s7)
    (hra : Section413G1Denote.NotIn8 ra s0 s1 s2 s3 s4 s5 s6 s7)
    (hrb : Section413G1Denote.NotIn8 rb s0 s1 s2 s3 s4 s5 s6 s7)
    (hrlo : Section413G1Denote.NotIn8 rlo s0 s1 s2 s3 s4 s5 s6 s7)
    (hrhi : Section413G1Denote.NotIn8 rhi s0 s1 s2 s3 s4 s5 s6 s7)
    (hlohi : rlo ≠ rhi) (hword : ∀ j, st.regs j < M) :
    let out := arun k st
      (CDEMAbelScan.mulWideBody ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7)
    out.regs rlo + MulWide.B64 * out.regs rhi = st.regs ra * st.regs rb ∧
      out.arr = st.arr := by
  have hrun := mulWideBody_arun_limbs k st ra rb rlo rhi
    s0 s1 s2 s3 s4 s5 s6 s7 hD hra hrb hrlo hrhi hlohi hword
  have hMB : M = MulWide.B64 := by decide
  have hspec := MulWide.hl_spec (st.regs ra) (st.regs rb)
    (by rw [← hMB]; exact hword ra)
    (by rw [← hMB]; exact hword rb)
  dsimp only at hrun ⊢
  have hlo := congrArg Prod.fst hrun.1
  have hhi := congrArg Prod.snd hrun.1
  constructor
  · simp only at hlo hhi
    rw [hlo, hhi]
    exact hspec.1
  · exact hrun.2

/-! ## Wide accumulation -/

/-- Scalar view of the literal CDEM accumulator.  Its argument order differs
from `AddWidePort.addWideBody`, so keeping this bridge explicit prevents a
carry/addend permutation from being hidden by elaboration. -/
def addWideS (accLo accHi alo ahi carry : Nat) : List Instr :=
  AddWidePort.addWideBody accLo accHi carry alo ahi

theorem addWideBody_lift (accLo accHi alo ahi carry : Nat) :
    CDEMAbelScan.addWideBody accLo accHi alo ahi carry =
      lift (addWideS accLo accHi alo ahi carry) := rfl

/-- The scalar view of CDEM's four accumulator instructions computes
`Verified.AddWide.addWide`, including the frame for every non-output register. -/
theorem addWideS_run (k : Nat) (s : RegState)
    (accLo accHi alo ahi carry : Nat)
    (hr : AddWidePort.WideRegs accLo accHi carry alo ahi) :
    let out := srun k s (addWideS accLo accHi alo ahi carry)
    (out accLo, out accHi) = AddWide.addWide (s accLo, s accHi) (s alo, s ahi) ∧
      ∀ j, j ≠ accLo → j ≠ accHi → j ≠ carry → out j = s j := by
  have hnodiv : ∀ i ∈ addWideS accLo accHi alo ahi carry, NoDivI i = true := by
    intro i hi
    simp only [addWideS, AddWidePort.addWideBody, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl
  have hmachine := srun_correct k _ hnodiv s
  obtain ⟨s', hdenote, hlo, hhi, hframe⟩ :=
    AddWidePort.addWideBody_denote accLo accHi carry alo ahi hr k s
  have heq : s' = srun k s (addWideS accLo accHi alo ahi carry) := by
    apply Option.some.inj
    exact hdenote.symm.trans hmachine
  subst s'
  exact ⟨Prod.ext hlo hhi, hframe⟩

/-- The literal CDEM accumulator computes wide addition and cannot modify the
array. -/
theorem addWideBody_arun (k : Nat) (st : AState)
    (accLo accHi alo ahi carry : Nat)
    (hr : AddWidePort.WideRegs accLo accHi carry alo ahi) :
    let out := arun k st (CDEMAbelScan.addWideBody accLo accHi alo ahi carry)
    (out.regs accLo, out.regs accHi) =
        AddWide.addWide (st.regs accLo, st.regs accHi) (st.regs alo, st.regs ahi) ∧
      out.arr = st.arr ∧
      ∀ j, j ≠ accLo → j ≠ accHi → j ≠ carry → out.regs j = st.regs j := by
  rw [addWideBody_lift, arun_lift]
  have h := addWideS_run k st.regs accLo accHi alo ahi carry hr
  exact ⟨h.1, rfl, h.2⟩

/-- Recombining the CDEM accumulator's output limbs gives addition modulo
`2^128`. -/
theorem addWideBody_arun_mod (k : Nat) (st : AState)
    (accLo accHi alo ahi carry : Nat)
    (hr : AddWidePort.WideRegs accLo accHi carry alo ahi)
    (hacc : AddWide.Ok (st.regs accLo, st.regs accHi))
    (hadd : AddWide.Ok (st.regs alo, st.regs ahi)) :
    let out := arun k st (CDEMAbelScan.addWideBody accLo accHi alo ahi carry)
    AddWide.wval (out.regs accLo, out.regs accHi) =
      (AddWide.wval (st.regs accLo, st.regs accHi) +
        AddWide.wval (st.regs alo, st.regs ahi)) % AddWide.B128 := by
  have hrun := addWideBody_arun k st accLo accHi alo ahi carry hr
  dsimp only at hrun ⊢
  rw [hrun.1]
  exact AddWide.addWide_spec _ _ hacc hadd

/-- Under the scan's no-overflow invariant, CDEM's accumulator is ordinary
exact natural-number addition. -/
theorem addWideBody_arun_exact (k : Nat) (st : AState)
    (accLo accHi alo ahi carry : Nat)
    (hr : AddWidePort.WideRegs accLo accHi carry alo ahi)
    (hacc : AddWide.Ok (st.regs accLo, st.regs accHi))
    (hadd : AddWide.Ok (st.regs alo, st.regs ahi))
    (hfit : AddWide.wval (st.regs accLo, st.regs accHi) +
      AddWide.wval (st.regs alo, st.regs ahi) < AddWide.B128) :
    let out := arun k st (CDEMAbelScan.addWideBody accLo accHi alo ahi carry)
    AddWide.wval (out.regs accLo, out.regs accHi) =
      AddWide.wval (st.regs accLo, st.regs accHi) +
        AddWide.wval (st.regs alo, st.regs ahi) := by
  dsimp only
  rw [addWideBody_arun_mod k st accLo accHi alo ahi carry hr hacc hadd,
    Nat.mod_eq_of_lt hfit]

/-! ## Exact-predicate arithmetic -/

/-- The branch structure implemented by CDEM's exact square predicate after
`W = a*s+b` has been computed. -/
def okFormula (s k a b : Nat) : Prop :=
  a * a ≤ k ∧
    ((k = a * a ∧ b = 0) ∨
      (k ≠ a * a ∧
        (2 * a + 1 ≤ k - a * a ∨
          (2 * a * b ≤ s * (k - a * a) ∧
            b * b ≤ s * (s * (k - a * a) - 2 * a * b)))))

/-- `(u+t)^2`, spelled out because LeanCompCert deliberately has no `ring`
dependency. -/
theorem sq_add (u t : Nat) :
    (u + t) * (u + t) = u * u + 2 * u * t + t * t := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.two_mul, Nat.mul_comm t u]
  omega

def residualFormula (s a b e : Nat) : Prop :=
  (e = 0 ∧ b = 0) ∨
    (e ≠ 0 ∧
      (2 * a + 1 ≤ e ∨
        (2 * a * b ≤ s * e ∧ b * b ≤ s * (s * e - 2 * a * b))))

theorem residualFormula_iff (s a b e : Nat) (hs : 0 < s) (hb : b < s) :
    residualFormula s a b e ↔
      2 * a * s * b + b * b ≤ s * s * e := by
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨he, hbig | hfine⟩)
    · simp
    · have hb' : b ≤ s := by omega
      have h1 : 2 * a * s * b ≤ 2 * a * s * s :=
        Nat.mul_le_mul_left (2 * a * s) hb'
      have h2 : b * b < s * s := Nat.mul_lt_mul_of_lt_of_lt hb hb
      have hsum : 2 * a * s * b + b * b < 2 * a * s * s + s * s :=
        Nat.add_lt_add_of_le_of_lt h1 h2
      have hid : 2 * a * s * s + s * s = s * s * (2 * a + 1) := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hmul : s * s * (2 * a + 1) ≤ s * s * e :=
        Nat.mul_le_mul_left (s * s) hbig
      omega
    · obtain ⟨hse, hlast⟩ := hfine
      have hsub : s * e - 2 * a * b + 2 * a * b = s * e :=
        Nat.sub_add_cancel hse
      have hid : s * s * e =
          2 * a * s * b + s * (s * e - 2 * a * b) := by
        calc
          s * s * e = s * (s * e) := by rw [Nat.mul_assoc]
          _ = s * ((s * e - 2 * a * b) + 2 * a * b) := by rw [hsub]
          _ = 2 * a * s * b + s * (s * e - 2 * a * b) := by
            simp [Nat.mul_add, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm]
      rw [hid]
      exact Nat.add_le_add_left hlast _
  · intro h
    by_cases he0 : e = 0
    · left
      refine ⟨he0, ?_⟩
      subst e
      simp only [Nat.mul_zero] at h
      cases b <;> simp at h ⊢
    · right
      refine ⟨he0, ?_⟩
      by_cases hbig : 2 * a + 1 ≤ e
      · exact Or.inl hbig
      · right
        have hse : 2 * a * b ≤ s * e := by
          apply Nat.le_of_not_gt
          intro hlt
          have hmul : s * (s * e) < s * (2 * a * b) :=
            Nat.mul_lt_mul_of_pos_left hlt hs
          have hleft : s * (2 * a * b) = 2 * a * s * b := by
            calc
              s * (2 * a * b) = (s * (2 * a)) * b := by rw [← Nat.mul_assoc]
              _ = ((2 * a) * s) * b := by rw [Nat.mul_comm s (2 * a)]
              _ = 2 * a * s * b := rfl
          have hright : s * (s * e) = s * s * e := by rw [Nat.mul_assoc]
          omega
        refine ⟨hse, ?_⟩
        have hsub : s * e - 2 * a * b + 2 * a * b = s * e :=
          Nat.sub_add_cancel hse
        have hid : s * s * e =
            2 * a * s * b + s * (s * e - 2 * a * b) := by
          calc
            s * s * e = s * (s * e) := by rw [Nat.mul_assoc]
            _ = s * ((s * e - 2 * a * b) + 2 * a * b) := by rw [hsub]
            _ = 2 * a * s * b + s * (s * e - 2 * a * b) := by
              simp [Nat.mul_add, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm]
        rw [hid] at h
        omega

/-- **The rearranged branch formula is exactly `s²*k ≥ W²`.**  This is the
paper-facing arithmetic theorem behind `okBody`: the large-`e` shortcut and
the fine 128-bit comparison are neither approximations nor one-way guards. -/
theorem okFormula_iff (W s k a b : Nat) (hs : 0 < s) (hb : b < s)
    (hW : W = a * s + b) :
    okFormula s k a b ↔ W * W ≤ s * s * k := by
  constructor
  · rintro ⟨hk, hcases⟩
    have hresFormula : residualFormula s a b (k - a * a) := by
      rcases hcases with hEq | hGt
      · rcases hEq with ⟨heq, hb0⟩
        left
        exact ⟨by omega, hb0⟩
      · rcases hGt with ⟨hne, hrest⟩
        right
        exact ⟨by omega, hrest⟩
    have hres := (residualFormula_iff s a b (k - a * a) hs hb).mp hresFormula
    have hsplit : k = a * a + (k - a * a) := by omega
    have hWsq : W * W =
        a * a * (s * s) + (2 * a * s * b + b * b) := by
      rw [hW]
      have h := sq_add (a * s) b
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    have hksq : s * s * k =
        a * a * (s * s) + s * s * (k - a * a) := by
      calc
        s * s * k = s * s * (a * a + (k - a * a)) := by rw [← hsplit]
        _ = a * a * (s * s) + s * s * (k - a * a) := by
          simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  · intro h
    have hk : a * a ≤ k := by
      apply Nat.le_of_not_gt
      intro hlt
      have hmul : s * s * k < s * s * (a * a) :=
        Nat.mul_lt_mul_of_pos_left hlt (Nat.mul_pos hs hs)
      have hWas : a * s ≤ W := by omega
      have hsq : (a * s) * (a * s) ≤ W * W := Nat.mul_le_mul hWas hWas
      have hid : (a * s) * (a * s) = s * s * (a * a) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm]
      rw [hid] at hsq
      omega
    refine ⟨hk, ?_⟩
    have hsplit : k = a * a + (k - a * a) := by omega
    have hWsq : W * W =
        a * a * (s * s) + (2 * a * s * b + b * b) := by
      rw [hW]
      have hsquare := sq_add (a * s) b
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsquare
    have hksq : s * s * k =
        a * a * (s * s) + s * s * (k - a * a) := by
      calc
        s * s * k = s * s * (a * a + (k - a * a)) := by rw [← hsplit]
        _ = a * a * (s * s) + s * s * (k - a * a) := by
          simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hres : 2 * a * s * b + b * b ≤ s * s * (k - a * a) := by
      omega
    have hform := (residualFormula_iff s a b (k - a * a) hs hb).mpr hres
    rcases hform with ⟨he0, hb0⟩ | ⟨hne0, hrest⟩
    · left
      exact ⟨by omega, hb0⟩
    · right
      exact ⟨by omega, hrest⟩

/-! ## Exact-predicate definedness

`okBody` contains the only register-valued divisions in the reciprocal-square-
root predicate.  Expanding all 63 instructions in one `simp` produces a
quadratic state term.  The proof therefore uses the intended scalar-block
boundary: two instructions manufacture a nonzero divisor, two perform the
division and remainder, and the entire tail is division-free.
-/

/-- Scalar view of the literal CDEM predicate block. -/
def okS (c : CDEMAbelScan.Cfg) (rs gate ok : Nat) : List Instr :=
  (CDEMAbelScan.okBody c rs gate ok).map Section413G1Denote.scalarOf

theorem okBody_lift (c : CDEMAbelScan.Cfg) (rs gate ok : Nat) :
    CDEMAbelScan.okBody c rs gate ok = lift (okS c rs gate ok) := by
  simp [okS, CDEMAbelScan.okBody, CDEMAbelScan.mulWideBody,
    Section413G1Denote.scalarOf, lift]

def okGuardS (rs : Nat) : List Instr :=
  [ .binop 100 .eq (.reg rs) (.lit 0)
  , .binop 100 .add (.reg 100) (.reg rs) ]

def okDivS (c : CDEMAbelScan.Cfg) : List Instr :=
  [ .binop 101 .udiv (.lit c.wScale) (.reg 100)
  , .binop 102 .urem (.lit c.wScale) (.reg 100) ]

def okRestS (c : CDEMAbelScan.Cfg) (rs gate ok : Nat) : List Instr :=
  (okS c rs gate ok).drop 4

theorem okS_decomp (c : CDEMAbelScan.Cfg) (rs gate ok : Nat) :
    okS c rs gate ok = okGuardS rs ++ okDivS c ++ okRestS c rs gate ok := by
  simp [okS, okGuardS, okDivS, okRestS, CDEMAbelScan.okBody,
    CDEMAbelScan.mulWideBody, Section413G1Denote.scalarOf]

/-- The guarded divisor is `1` at `s = 0` and `s` otherwise.  The register
separation hypothesis is exactly the instruction-order condition needed to
read the input after scratch register `100` is written. -/
theorem okGuard_denominator (k : Nat) (s : RegState) (rs : Nat)
    (hrs100 : rs ≠ 100) (hrs : s rs < M) :
    srun k s (okGuardS rs) 100 ≠ 0 := by
  have hM1 : M ≠ 1 := by decide
  by_cases hz : s rs = 0
  · simp [okGuardS, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, hz, hrs100, hM1]
  · have hmod : s rs % M = s rs := Nat.mod_eq_of_lt hrs
    simp [okGuardS, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, hz, hrs100, hmod]

theorem okDiv_defined (c : CDEMAbelScan.Cfg) (len k : Nat) (st : AState)
    (hden : st.regs 100 ≠ 0) :
    AllDefined len k st (lift (okDivS c)) := by
  simp [okDivS, lift, AllDefined, ADefined, hden, astep, sdest, sval,
    denoteOperand, denoteOp, AState.writeReg]

/-- The four-instruction quotient prefix of the literal predicate. -/
def okQuotS (c : CDEMAbelScan.Cfg) (rs : Nat) : List Instr :=
  okGuardS rs ++ okDivS c

/-- For a positive word candidate and a word-sized weight, the literal prefix
computes the Euclidean quotient and remainder used by `okFormula`. -/
theorem okQuot_arun (c : CDEMAbelScan.Cfg) (k : Nat) (st : AState)
    (rs : Nat) (hrs100 : rs ≠ 100) (hs : 0 < st.regs rs)
    (hsM : st.regs rs < M) (hW : c.wScale < M) :
    let out := arun k st (lift (okQuotS c rs))
    out.regs 100 = st.regs rs ∧
      out.regs 101 = c.wScale / st.regs rs ∧
      out.regs 102 = c.wScale % st.regs rs ∧
      out.arr = st.arr := by
  have hs0 : st.regs rs ≠ 0 := Nat.ne_of_gt hs
  have hsmod : st.regs rs % M = st.regs rs := Nat.mod_eq_of_lt hsM
  have hWmod : c.wScale % M = c.wScale := Nat.mod_eq_of_lt hW
  have hdivM : c.wScale / st.regs rs < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hW
  have hremM : c.wScale % st.regs rs < M :=
    Nat.lt_trans (Nat.mod_lt _ hs) hsM
  rw [arun_lift]
  simp [okQuotS, okGuardS, okDivS, srun, sdest, sval, denoteOperand,
    denoteOp, RegState.set, hs0, hrs100, hsmod, hWmod,
    Nat.mod_eq_of_lt hdivM, Nat.mod_eq_of_lt hremM]

/-- Exact non-wrapping subtraction in the fragment's modular encoding. -/
theorem msub_exact (x y : Nat) (hyx : y ≤ x) (hx : x < M) :
    (x + (M - y)) % M = x - y := by
  have hyM : y ≤ M := by omega
  have h : x + (M - y) = (x - y) + M := by omega
  rw [h, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- The production predicate's classification stage, immediately after the
quotient/remainder prefix.  Registers `142`, `rK`, `rViol`, and `rVDiv` are
the literal allocation in `Cfg.accBisect`. -/
def okClassifyS : List Instr :=
  [ .mov 100 (.reg 101)
  , .mov 101 (.reg 102)
  , .binop 102 .gt (.reg 100) (.lit 2147483648)
  , .binop 102 .mul (.reg 102) (.reg 142)
  , .binop CDEMAbelScan.rViol .add (.reg CDEMAbelScan.rViol) (.reg 102)
  , .binop CDEMAbelScan.rVDiv .add (.reg CDEMAbelScan.rVDiv) (.reg 102)
  , .binop 103 .mul (.reg 100) (.reg 100)
  , .binop 104 .lt (.reg CDEMAbelScan.rK) (.reg 103)
  , .binop 105 .sub (.lit 1) (.reg 104)
  , .binop 106 .eq (.reg CDEMAbelScan.rK) (.reg 103)
  , .binop 107 .sub (.lit 1) (.reg 106)
  , .binop 108 .eq (.reg 101) (.lit 0)
  , .binop 109 .sub (.reg CDEMAbelScan.rK) (.reg 103)
  , .binop 110 .mul (.reg 100) (.lit 2)
  , .binop 110 .add (.reg 110) (.lit 1)
  , .binop 111 .ge (.reg 109) (.reg 110)
  , .binop 112 .sub (.lit 1) (.reg 111) ]

/-- Under the exact word bounds used by the live bisection regime, the
classification stage computes the first half of `okFormula`. -/
theorem okClassify_run (idx : Nat) (s : RegState) (a b k : Nat)
    (ha : s 101 = a) (hb : s 102 = b) (hk : s CDEMAbelScan.rK = k)
    (haSqM : a * a < M) (hka : a * a ≤ k) (hkM : k < M)
    (h2aM : 2 * a + 1 < M) :
    let out := srun idx s okClassifyS
    out 100 = a ∧ out 101 = b ∧ out 103 = a * a ∧
      out 105 = 1 ∧
      out 106 = (if k = a * a then 1 else 0) ∧
      out 107 = (if k ≠ a * a then 1 else 0) ∧
      out 108 = (if b = 0 then 1 else 0) ∧
      out 109 = k - a * a ∧ out 110 = 2 * a + 1 ∧
      out 111 = (if 2 * a + 1 ≤ k - a * a then 1 else 0) ∧
      out 112 = (if ¬2 * a + 1 ≤ k - a * a then 1 else 0) := by
  have h2M : (2:Nat) % M = 2 := by decide
  have h1M : (1:Nat) % M = 1 := by decide
  have h0M : (0:Nat) % M = 0 := by decide
  have he : (k + (M - a * a)) % M = k - a * a :=
    msub_exact k (a * a) hka hkM
  have hk30 : s 30 = k := by simpa [CDEMAbelScan.rK] using hk
  have ha2M : a * 2 < M := by omega
  have ha2mod : a * 2 % M = a * 2 := Nat.mod_eq_of_lt ha2M
  have ha2sum : (a * 2 + 1) % M = 2 * a + 1 := by
    rw [Nat.mul_comm a 2, Nat.mod_eq_of_lt h2aM]
  have hbit (P : Prop) [Decidable P] : (if P then (1:Nat) else 0) ≤ 1 := by
    split <;> omega
  simp only [okClassifyS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, CDEMAbelScan.rK, CDEMAbelScan.rViol,
    CDEMAbelScan.rVDiv, reduceIte, Nat.reduceEqDiff, ha, hb, h2M, h1M,
    h0M, Nat.mod_eq_of_lt haSqM]
  simp only [hk30, he, ha2mod, show ¬k < a * a from by omega,
    if_false, Section413G1Denote.msub_bit (hbit (k = a * a))]
  rw [ha2sum]
  by_cases heq : k = a * a <;>
    by_cases hbig : 2 * a + 1 ≤ k - a * a <;>
    simp [heq, hbig, h1M]
  all_goals decide

/-- Tail after the quotient and classification stages in the one live use of
`okBody` (`rs=194`, gate `142`, result `197`). -/
def okAfterClassifyS (c : CDEMAbelScan.Cfg) : List Instr :=
  (okS c 194 142 197).drop 21

theorem productionOkS_decomp (c : CDEMAbelScan.Cfg) :
    okS c 194 142 197 =
      okQuotS c 194 ++ okClassifyS ++ okAfterClassifyS c := by
  simp [okS, okQuotS, okGuardS, okDivS, okClassifyS, okAfterClassifyS,
    CDEMAbelScan.okBody, CDEMAbelScan.mulWideBody,
    Section413G1Denote.scalarOf]

/-- The full literal predicate block cannot fail through division by zero.
No semantic claim is hidden here: correctness of the Boolean result remains a
separate refinement theorem, while this theorem closes partial definedness. -/
theorem okBody_defined (c : CDEMAbelScan.Cfg) (len k : Nat) (st : AState)
    (rs gate ok : Nat) (hrs100 : rs ≠ 100) (hrs : st.regs rs < M) :
    AllDefined len k st (CDEMAbelScan.okBody c rs gate ok) := by
  rw [okBody_lift, okS_decomp, lift_append, lift_append,
    AllDefined_append, AllDefined_append]
  refine ⟨⟨allDefined_lift_of_noDiv len k _ st (by rfl), ?_⟩, ?_⟩
  · apply okDiv_defined
    rw [arun_lift]
    exact okGuard_denominator k st.regs rs hrs100 hrs
  · apply allDefined_lift_of_noDiv
    rfl

end LeanCompCert.Ports.CDEMAbelPrimitives

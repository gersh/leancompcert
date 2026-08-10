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

instance (s k a b : Nat) : Decidable (okFormula s k a b) := by
  unfold okFormula
  infer_instance

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
root predicate.  Expanding all 74 instructions in one `simp` produces a
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

theorem okQuot_run (c : CDEMAbelScan.Cfg) (idx : Nat) (r : RegState)
    (rs : Nat) (hrs100 : rs ≠ 100) (hs : 0 < r rs)
    (hsM : r rs < M) (hW : c.wScale < M) :
    let out := srun idx r (okQuotS c rs)
    out 100 = r rs ∧ out 101 = c.wScale / r rs ∧
      out 102 = c.wScale % r rs := by
  let st : AState := { regs := r, arr := fun _ => 0 }
  have h := okQuot_arun c idx st rs hrs100 hs hsM hW
  dsimp only [st] at h
  rw [arun_lift] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem okQuot_frame (c : CDEMAbelScan.Cfg) (idx : Nat) (r : RegState)
    (rs j : Nat) (hj100 : j ≠ 100) (hj101 : j ≠ 101) (hj102 : j ≠ 102) :
    srun idx r (okQuotS c rs) j = r j := by
  apply srun_untouched
  intro i hi
  simp only [okQuotS, okGuardS, okDivS, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl) | (rfl | rfl) <;>
    simp only [sdest] <;> omega

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

/-- If `k < a²`, the classification gate is zero.  No subtraction value is
claimed in this branch; the remaining predicate is killed by this gate. -/
theorem okClassify_false105 (idx : Nat) (r : RegState) (a k : Nat)
    (ha : r 101 = a) (hk : r CDEMAbelScan.rK = k)
    (haSqM : a * a < M) (hka : k < a * a) :
    srun idx r okClassifyS 105 = 0 := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hzero : (1 + (M - 1)) % M = 0 := by decide
  have hk30 : r 30 = k := by simpa [CDEMAbelScan.rK] using hk
  simp only [okClassifyS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, CDEMAbelScan.rK, CDEMAbelScan.rViol,
    CDEMAbelScan.rVDiv, reduceIte, Nat.reduceEqDiff, ha,
    Nat.mod_eq_of_lt haSqM, hk30, h1M]
  simp [hka, hzero]

theorem okClassify_frame (idx : Nat) (r : RegState) (j : Nat)
    (hj : 112 < j)
    (hViol : j ≠ CDEMAbelScan.rViol)
    (hVDiv : j ≠ CDEMAbelScan.rVDiv) :
    srun idx r okClassifyS j = r j := by
  apply srun_untouched
  intro i hi
  simp only [okClassifyS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

/-! ## Exact-predicate product and comparison tail -/

/-- The five scalar instructions between classification and the two wide
products in the production predicate. -/
def okProductPrepS : List Instr :=
  [ .binop 113 .mul (.reg 194) (.reg 109)
  , .binop 114 .mul (.reg 100) (.reg 101)
  , .binop 114 .mul (.reg 114) (.lit 2)
  , .binop 115 .ge (.reg 113) (.reg 114)
  , .binop 116 .sub (.reg 113) (.reg 114) ]

/-- The comparison flag is exact even when the following subtraction would
wrap.  This is the branch fact used to gate the wide comparison off. -/
theorem okProductPrep_flags (idx : Nat) (r : RegState) (s e a b : Nat)
    (hs : r 194 = s) (he : r 109 = e) (ha : r 100 = a) (hb : r 101 = b)
    (hseM : s * e < M) (habM : a * b < M) (h2abM : 2 * a * b < M) :
    let out := srun idx r okProductPrepS
    out 113 = s * e ∧ out 114 = 2 * a * b ∧
      out 115 = (if 2 * a * b ≤ s * e then 1 else 0) := by
  have h2M : (2 : Nat) % M = 2 := by decide
  have hse : (s * e) % M = s * e := Nat.mod_eq_of_lt hseM
  have hab : (a * b) % M = a * b := Nat.mod_eq_of_lt habM
  have h2ab : (a * b * 2) % M = 2 * a * b := by
    have hid : a * b * 2 = 2 * a * b := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hid, Nat.mod_eq_of_lt h2abM]
  simp only [okProductPrepS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, reduceIte, Nat.reduceEqDiff,
    hs, he, ha, hb, h2M, hse, hab, h2ab]
  by_cases hle : 2 * a * b ≤ s * e <;> simp

/-- In the fine predicate branch, the product-preparation instructions are
ordinary exact natural-number arithmetic.  The explicit bounds are the
machine-word obligations later supplied by the bisection invariant. -/
theorem okProductPrep_run (idx : Nat) (r : RegState) (s e a b : Nat)
    (hs : r 194 = s) (he : r 109 = e) (ha : r 100 = a) (hb : r 101 = b)
    (hseM : s * e < M) (habM : a * b < M) (h2abM : 2 * a * b < M)
    (hle : 2 * a * b ≤ s * e) :
    let out := srun idx r okProductPrepS
    out 113 = s * e ∧ out 114 = 2 * a * b ∧ out 115 = 1 ∧
      out 116 = s * e - 2 * a * b := by
  have h2M : (2 : Nat) % M = 2 := by decide
  have hse : (s * e) % M = s * e := Nat.mod_eq_of_lt hseM
  have hab : (a * b) % M = a * b := Nat.mod_eq_of_lt habM
  have h2ab : (a * b * 2) % M = 2 * a * b := by
    have hid : a * b * 2 = 2 * a * b := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hid, Nat.mod_eq_of_lt h2abM]
  have hsub := msub_exact (s * e) (2 * a * b) hle hseM
  simp only [okProductPrepS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, reduceIte, Nat.reduceEqDiff,
    hs, he, ha, hb, h2M, hse, hab, h2ab, hsub]
  simp [hle]

theorem okProductPrep_frame (idx : Nat) (r : RegState) (j : Nat)
    (h113 : j ≠ 113) (h114 : j ≠ 114) (h115 : j ≠ 115)
    (h116 : j ≠ 116) :
    srun idx r okProductPrepS j = r j := by
  apply srun_untouched
  intro i hi
  simp only [okProductPrepS, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> omega

/-- Lexicographic comparison of two little-endian 64-bit limb pairs. -/
def wordGe (lo1 hi1 lo2 hi2 : Nat) : Prop :=
  hi2 < hi1 ∨ (hi1 = hi2 ∧ lo2 ≤ lo1)

/-- Lexicographic limb comparison is exactly comparison of the recombined
128-bit naturals. -/
theorem wordGe_iff_wval (lo1 hi1 lo2 hi2 : Nat)
    (hlo1 : lo1 < MulWide.B64) (hlo2 : lo2 < MulWide.B64) :
    wordGe lo1 hi1 lo2 hi2 ↔
      lo2 + MulWide.B64 * hi2 ≤ lo1 + MulWide.B64 * hi1 := by
  unfold wordGe
  simp only [MulWide.B64] at hlo1 hlo2 ⊢
  omega

/-- The final twelve scalar instructions of the production predicate. -/
def okPostS : List Instr :=
  [ .binop 129 .gt (.reg 118) (.reg 128)
  , .binop 120 .eq (.reg 118) (.reg 128)
  , .binop 121 .ge (.reg 117) (.reg 119)
  , .binop 120 .mul (.reg 120) (.reg 121)
  , .binop 129 .add (.reg 129) (.reg 120)
  , .binop 129 .mul (.reg 129) (.reg 115)
  , .binop 129 .mul (.reg 129) (.reg 112)
  , .binop 129 .add (.reg 129) (.reg 111)
  , .binop 129 .mul (.reg 129) (.reg 107)
  , .binop 122 .mul (.reg 106) (.reg 108)
  , .binop 129 .add (.reg 129) (.reg 122)
  , .binop 197 .mul (.reg 129) (.reg 105) ]

/-- Assuming the classification flags have their proved Boolean meanings,
the literal postlude implements the disjunction structure of `okFormula`.
The `Neq ↔ ¬Eq` hypothesis is important: it excludes impossible flag sums
before modular word normalization. -/
theorem okPost_run (idx : Nat) (r : RegState)
    (A Eq Neq B0 Big Se : Prop) [Decidable A] [Decidable Eq]
    [Decidable Neq] [Decidable B0] [Decidable Big] [Decidable Se]
    (lo1 hi1 lo2 hi2 : Nat)
    [Decidable (wordGe lo1 hi1 lo2 hi2)]
    (hNeqIff : Neq ↔ ¬Eq)
    (h105 : r 105 = if A then 1 else 0)
    (h106 : r 106 = if Eq then 1 else 0)
    (h107 : r 107 = if Neq then 1 else 0)
    (h108 : r 108 = if B0 then 1 else 0)
    (h111 : r 111 = if Big then 1 else 0)
    (h112 : r 112 = if ¬Big then 1 else 0)
    (h115 : r 115 = if Se then 1 else 0)
    (h117 : r 117 = lo1) (h118 : r 118 = hi1)
    (h119 : r 119 = lo2) (h128 : r 128 = hi2) :
    srun idx r okPostS 197 =
      if A ∧ ((Eq ∧ B0) ∨ (Neq ∧ (Big ∨ (Se ∧ wordGe lo1 hi1 lo2 hi2))))
      then 1 else 0 := by
  have hNeqEq : Neq = ¬Eq := propext hNeqIff
  subst Neq
  simp only [okPostS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, reduceIte, Nat.reduceEqDiff,
    h105, h106, h107, h108, h111, h112, h115, h117, h118, h119, h128]
  unfold wordGe
  by_cases hA : A <;> by_cases hEq : Eq <;>
    by_cases hB0 : B0 <;> by_cases hBig : Big <;> by_cases hSe : Se <;>
    by_cases hHi : hi2 < hi1 <;> by_cases hHiEq : hi1 = hi2 <;>
    by_cases hLo : lo2 ≤ lo1 <;> simp [hA, hEq, hB0, hBig, hSe,
      hHi, hHiEq, hLo]
  all_goals decide

/-- The final production gate dominates every preceding flag and comparison. -/
theorem okPost_zero (idx : Nat) (r : RegState) (h105 : r 105 = 0) :
    srun idx r okPostS 197 = 0 := by
  simp [okPostS, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, h105]

/-- The two literal half-limb multipliers in the production predicate, in
their scalar form. -/
def okMul1S : List Instr :=
  Section413G1Denote.mulWideG 4294967295 4294967296
    194 116 117 118 120 121 122 123 124 125 126 127

def okMul2S : List Instr :=
  Section413G1Denote.mulWideG 4294967295 4294967296
    101 101 119 128 120 121 122 123 124 125 126 127

theorem okMul1_frame (idx : Nat) (r : RegState) (j : Nat)
    (hlo : j ≠ 117) (hhi : j ≠ 118)
    (hj : Section413G1Denote.NotIn8 j 120 121 122 123 124 125 126 127) :
    srun idx r okMul1S j = r j :=
  Section413G1Denote.mulWideG_frame idx r 4294967295 4294967296
    194 116 117 118 120 121 122 123 124 125 126 127 j hlo hhi hj

theorem okMul2_frame (idx : Nat) (r : RegState) (j : Nat)
    (hlo : j ≠ 119) (hhi : j ≠ 128)
    (hj : Section413G1Denote.NotIn8 j 120 121 122 123 124 125 126 127) :
    srun idx r okMul2S j = r j :=
  Section413G1Denote.mulWideG_frame idx r 4294967295 4294967296
    101 101 119 128 120 121 122 123 124 125 126 127 j hlo hhi hj

theorem okMul1_limbs (idx : Nat) (r : RegState) (hword : ∀ j, r j < M) :
    srun idx r okMul1S 117 = (MulWide.hl (r 194) (r 116)).1 ∧
      srun idx r okMul1S 118 = (MulWide.hl (r 194) (r 116)).2 := by
  exact Section413G1Denote.mulWideG_hl idx r 194 116 117 118
    120 121 122 123 124 125 126 127
    (by simp [Section413G1Denote.Distinct8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8]) (by decide) hword

theorem okMul2_limbs (idx : Nat) (r : RegState) (hword : ∀ j, r j < M) :
    srun idx r okMul2S 119 = (MulWide.hl (r 101) (r 101)).1 ∧
      srun idx r okMul2S 128 = (MulWide.hl (r 101) (r 101)).2 := by
  exact Section413G1Denote.mulWideG_hl idx r 101 101 119 128
    120 121 122 123 124 125 126 127
    (by simp [Section413G1Denote.Distinct8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8])
    (by simp [Section413G1Denote.NotIn8]) (by decide) hword

/-- Tail after the quotient and classification stages in the one live use of
`okBody` (`rs=194`, gate `142`, result `197`). -/
def okAfterClassifyS (c : CDEMAbelScan.Cfg) : List Instr :=
  (okS c 194 142 197).drop 21

theorem okAfterClassifyS_decomp (c : CDEMAbelScan.Cfg) :
    okAfterClassifyS c =
      okProductPrepS ++ okMul1S ++ okMul2S ++ okPostS := by
  simp [okAfterClassifyS, okS, CDEMAbelScan.okBody,
    CDEMAbelScan.mulWideBody, Section413G1Denote.scalarOf,
    okProductPrepS, okMul1S, okMul2S, Section413G1Denote.mulWideG, okPostS]

theorem okAfterClassify_zero (c : CDEMAbelScan.Cfg) (idx : Nat)
    (r : RegState) (h105 : r 105 = 0) :
    srun idx r (okAfterClassifyS c) 197 = 0 := by
  let r1 := srun idx r okProductPrepS
  let r2 := srun idx r1 okMul1S
  let r3 := srun idx r2 okMul2S
  have hr1 : r1 105 = 0 := by
    have h := okProductPrep_frame idx r 105 (by decide) (by decide) (by decide)
      (by decide)
    simpa [r1, h105] using h
  have hr2 : r2 105 = 0 := by
    have h := okMul1_frame idx r1 105 (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8])
    simpa [r2, hr1] using h
  have hr3 : r3 105 = 0 := by
    have h := okMul2_frame idx r2 105 (by decide) (by decide)
      (by simp [Section413G1Denote.NotIn8])
    simpa [r3, hr2] using h
  rw [okAfterClassifyS_decomp, srun_append, srun_append, srun_append]
  exact okPost_zero idx r3 hr3

/-- The complete production tail refines the residual predicate formula.
The wrapping subtraction branch is handled separately: when it would wrap,
register `115` gates the ensuing wide product out of the Boolean result. -/
theorem okAfterClassify_run (c : CDEMAbelScan.Cfg) (idx : Nat)
    (r : RegState) (s e a b : Nat)
    (A Eq B0 Big : Prop) [Decidable A] [Decidable Eq]
    [Decidable B0] [Decidable Big]
    (hword : ∀ j, r j < M)
    (hs : r 194 = s) (he : r 109 = e) (ha : r 100 = a) (hb : r 101 = b)
    (h105 : r 105 = if A then 1 else 0)
    (h106 : r 106 = if Eq then 1 else 0)
    (h107 : r 107 = if ¬Eq then 1 else 0)
    (h108 : r 108 = if B0 then 1 else 0)
    (h111 : r 111 = if Big then 1 else 0)
    (h112 : r 112 = if ¬Big then 1 else 0)
    (hseM : s * e < M) (habM : a * b < M) (h2abM : 2 * a * b < M) :
    srun idx r (okAfterClassifyS c) 197 =
      if A ∧ ((Eq ∧ B0) ∨
        (¬Eq ∧ (Big ∨
          (2 * a * b ≤ s * e ∧ b * b ≤ s * (s * e - 2 * a * b)))))
      then 1 else 0 := by
  classical
  let r1 := srun idx r okProductPrepS
  let r2 := srun idx r1 okMul1S
  let r3 := srun idx r2 okMul2S
  have hr1word : ∀ j, r1 j < M := srun_lt_of_lt idx _ r hword
  have hr2word : ∀ j, r2 j < M := srun_lt_of_lt idx _ r1 hr1word
  have hr1frame (j : Nat) (hj : j ≤ 112 ∨ 116 < j) : r1 j = r j := by
    apply okProductPrep_frame <;> omega
  have hr2frame (j : Nat) (hj : j ≤ 116 ∨ 128 < j) : r2 j = r1 j := by
    apply okMul1_frame <;> simp [Section413G1Denote.NotIn8] <;> omega
  have hr3frame (j : Nat) (hj : j ≤ 118) : r3 j = r2 j := by
    apply okMul2_frame <;> simp [Section413G1Denote.NotIn8] <;> omega
  have hprep := okProductPrep_flags idx r s e a b hs he ha hb hseM habM h2abM
  dsimp only at hprep
  have h105' : r3 105 = if A then 1 else 0 := by
    rw [hr3frame 105 (by omega), hr2frame 105 (by omega),
      hr1frame 105 (by omega), h105]
  have h106' : r3 106 = if Eq then 1 else 0 := by
    rw [hr3frame 106 (by omega), hr2frame 106 (by omega),
      hr1frame 106 (by omega), h106]
  have h107' : r3 107 = if ¬Eq then 1 else 0 := by
    rw [hr3frame 107 (by omega), hr2frame 107 (by omega),
      hr1frame 107 (by omega), h107]
  have h108' : r3 108 = if B0 then 1 else 0 := by
    rw [hr3frame 108 (by omega), hr2frame 108 (by omega),
      hr1frame 108 (by omega), h108]
  have h111' : r3 111 = if Big then 1 else 0 := by
    rw [hr3frame 111 (by omega), hr2frame 111 (by omega),
      hr1frame 111 (by omega), h111]
  have h112' : r3 112 = if ¬Big then 1 else 0 := by
    rw [hr3frame 112 (by omega), hr2frame 112 (by omega),
      hr1frame 112 (by omega), h112]
  have h115' : r3 115 = if 2 * a * b ≤ s * e then 1 else 0 := by
    rw [hr3frame 115 (by omega), hr2frame 115 (by omega)]
    exact hprep.2.2
  rw [okAfterClassifyS_decomp, srun_append, srun_append, srun_append]
  change srun idx r3 okPostS 197 = _
  have hpost := okPost_run idx r3 A Eq (¬Eq) B0 Big
    (2 * a * b ≤ s * e) (r3 117) (r3 118) (r3 119) (r3 128)
    (by simp) h105' h106' h107' h108' h111' h112' h115'
    rfl rfl rfl rfl
  by_cases hle : 2 * a * b ≤ s * e
  · have hprepExact := okProductPrep_run idx r s e a b hs he ha hb
      hseM habM h2abM hle
    dsimp only at hprepExact
    have hr1s : r1 194 = s := by rw [hr1frame 194 (by omega), hs]
    have hr1b : r1 101 = b := by rw [hr1frame 101 (by omega), hb]
    have hr1d : r1 116 = s * e - 2 * a * b := hprepExact.2.2.2
    have hm1 := okMul1_limbs idx r1 hr1word
    have hm1lo : r2 117 = (MulWide.hl (r1 194) (r1 116)).1 := by
      simpa [r2] using hm1.1
    have hm1hi : r2 118 = (MulWide.hl (r1 194) (r1 116)).2 := by
      simpa [r2] using hm1.2
    have hm1spec := MulWide.hl_spec (r1 194) (r1 116)
      (hr1word 194) (hr1word 116)
    have hr2b : r2 101 = b := by rw [hr2frame 101 (by omega), hr1b]
    have hm2 := okMul2_limbs idx r2 hr2word
    have hm2lo : r3 119 = (MulWide.hl (r2 101) (r2 101)).1 := by
      simpa [r3] using hm2.1
    have hm2hi : r3 128 = (MulWide.hl (r2 101) (r2 101)).2 := by
      simpa [r3] using hm2.2
    have hm2spec := MulWide.hl_spec (r2 101) (r2 101)
      (hr2word 101) (hr2word 101)
    have hprod1 : r3 117 + MulWide.B64 * r3 118 =
        s * (s * e - 2 * a * b) := by
      rw [hr3frame 117 (by omega), hr3frame 118 (by omega), hm1lo, hm1hi,
        hm1spec.1, hr1s, hr1d]
    have hprod2 : r3 119 + MulWide.B64 * r3 128 = b * b := by
      rw [hm2lo, hm2hi, hm2spec.1, hr2b]
    have hlo1 : r3 117 < MulWide.B64 := by
      rw [hr3frame 117 (by omega), hm1lo]
      exact hm1spec.2
    have hlo2 : r3 119 < MulWide.B64 := by
      rw [hm2lo]
      exact hm2spec.2
    have hwordCmp : wordGe (r3 117) (r3 118) (r3 119) (r3 128) ↔
        b * b ≤ s * (s * e - 2 * a * b) := by
      rw [wordGe_iff_wval _ _ _ _ hlo1 hlo2, hprod1, hprod2]
    simp only [hwordCmp] at hpost
    simpa [hle] using hpost
  · simpa [hle] using hpost

theorem productionOkS_decomp (c : CDEMAbelScan.Cfg) :
    okS c 194 142 197 =
      okQuotS c 194 ++ okClassifyS ++ okAfterClassifyS c := by
  simp [okS, okQuotS, okGuardS, okDivS, okClassifyS, okAfterClassifyS,
    CDEMAbelScan.okBody, CDEMAbelScan.mulWideBody,
    Section413G1Denote.scalarOf]

/-- The entire 74-instruction predicate used by the live bisection site
returns the exact Boolean value of `okFormula`.  All word-fit obligations are
spelled out so that the enclosing bisection invariant, rather than a hidden
normalization assumption, supplies them. -/
theorem productionOkS_run (c : CDEMAbelScan.Cfg) (idx : Nat)
    (r : RegState) (s k : Nat)
    (hword : ∀ j, r j < M)
    (hs : r 194 = s) (hk : r CDEMAbelScan.rK = k)
    (hspos : 0 < s) (hW : c.wScale < M) (hkM : k < M)
    (haSqM : (c.wScale / s) * (c.wScale / s) < M)
    (h2aM : 2 * (c.wScale / s) + 1 < M)
    (hseM : s * (k - (c.wScale / s) * (c.wScale / s)) < M)
    (habM : (c.wScale / s) * (c.wScale % s) < M)
    (h2abM : 2 * (c.wScale / s) * (c.wScale % s) < M) :
    srun idx r (okS c 194 142 197) 197 =
      if okFormula s k (c.wScale / s) (c.wScale % s) then 1 else 0 := by
  let a := c.wScale / s
  let b := c.wScale % s
  let e := k - a * a
  let q := srun idx r (okQuotS c 194)
  let cl := srun idx q okClassifyS
  have hsM : s < M := by rw [← hs]; exact hword 194
  have hquot := okQuot_run c idx r 194 (by decide) (by simpa [hs] using hspos)
    (by simpa [hs] using hsM) hW
  dsimp only at hquot
  have hq100 : q 100 = s := by simpa [q, hs] using hquot.1
  have hq101 : q 101 = a := by simpa [q, a, hs] using hquot.2.1
  have hq102 : q 102 = b := by simpa [q, b, hs] using hquot.2.2
  have hq194 : q 194 = s := by
    have h := okQuot_frame c idx r 194 194 (by decide) (by decide) (by decide)
    simpa [q, hs] using h
  have hqk : q CDEMAbelScan.rK = k := by
    have h := okQuot_frame c idx r 194 CDEMAbelScan.rK
      (by simp [CDEMAbelScan.rK]) (by simp [CDEMAbelScan.rK])
      (by simp [CDEMAbelScan.rK])
    simpa [q, hk] using h
  have hqword : ∀ j, q j < M := srun_lt_of_lt idx _ r hword
  have hclword : ∀ j, cl j < M := srun_lt_of_lt idx _ q hqword
  have hcl194 : cl 194 = s := by
    have h := okClassify_frame idx q 194 (by omega)
      (by simp [CDEMAbelScan.rViol]) (by simp [CDEMAbelScan.rVDiv])
    simpa [cl, hq194] using h
  rw [productionOkS_decomp, srun_append, srun_append]
  change srun idx cl (okAfterClassifyS c) 197 = _
  by_cases hka : a * a ≤ k
  · have hclass := okClassify_run idx q a b k hq101 hq102 hqk
      (by simpa [a] using haSqM) hka hkM (by simpa [a] using h2aM)
    dsimp only at hclass
    rcases hclass with
      ⟨hc100, hc101, hc103, hc105, hc106, hc107, hc108, hc109,
        hc110, hc111, hc112⟩
    have htail := okAfterClassify_run c idx cl s e a b
      (a * a ≤ k) (k = a * a) (b = 0) (2 * a + 1 ≤ e)
      hclword hcl194 (by simpa [cl, e] using hc109)
      (by simpa [cl] using hc100) (by simpa [cl] using hc101)
      (by simpa [hka] using hc105)
      (by simpa [cl] using hc106) (by simpa [cl] using hc107)
      (by simpa [cl] using hc108) (by simpa [cl, e] using hc111)
      (by simpa [cl, e] using hc112)
      (by simpa [a, e] using hseM) (by simpa [a, b] using habM)
      (by simpa [a, b] using h2abM)
    simpa [okFormula, a, b, e, hka] using htail
  · have hlt : k < a * a := by omega
    have hfalse := okClassify_false105 idx q a k hq101 hqk
      (by simpa [a] using haSqM) hlt
    have hcl105 : cl 105 = 0 := by simpa [cl] using hfalse
    rw [okAfterClassify_zero c idx cl hcl105]
    simp [okFormula, a, hka]

/-- Paper-facing form of `productionOkS_run`: the literal block decides the
monotone square predicate used by bisection. -/
theorem productionOkS_run_sq (c : CDEMAbelScan.Cfg) (idx : Nat)
    (r : RegState) (s k : Nat)
    (hword : ∀ j, r j < M)
    (hs : r 194 = s) (hk : r CDEMAbelScan.rK = k)
    (hspos : 0 < s) (hW : c.wScale < M) (hkM : k < M)
    (haSqM : (c.wScale / s) * (c.wScale / s) < M)
    (h2aM : 2 * (c.wScale / s) + 1 < M)
    (hseM : s * (k - (c.wScale / s) * (c.wScale / s)) < M)
    (habM : (c.wScale / s) * (c.wScale % s) < M)
    (h2abM : 2 * (c.wScale / s) * (c.wScale % s) < M) :
    srun idx r (okS c 194 142 197) 197 =
      if c.wScale * c.wScale ≤ s * s * k then 1 else 0 := by
  rw [productionOkS_run c idx r s k hword hs hk hspos hW hkM
    haSqM h2aM hseM habM h2abM]
  have hWdecomp : c.wScale =
      (c.wScale / s) * s + c.wScale % s := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod c.wScale s).symm
  have hiff := okFormula_iff c.wScale s k (c.wScale / s)
    (c.wScale % s) hspos (Nat.mod_lt _ hspos) hWdecomp
  simp only [hiff]

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

import LeanCompCert.Verified.Algorithm.Spec
import LeanCompCert.Verified.BlockDefined
import LeanCompCert.Verified.FoldBridge

/-!
# A guarded harmonic-ceiling fold

This port computes

`sum_{i=0}^{len-1} (numerator + i) / (i + 1)`

in a scalar `Reflect.Program`.  Every iteration latches two checks: the
machine addition did not wrap, and the new partial sum is at most `bound`.
Consequently a final return value of `1` proves the corresponding unbounded
`Nat` fold is at most `bound`; modular arithmetic cannot create a false
acceptance.
-/

namespace LeanCompCert.Ports.CeHarmonicFold

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.FoldBridge
open LeanCompCert.Verified.Algorithm

structure Params where
  len : Nat
  numerator : Nat
  bound : Nat

def Params.Sane (c : Params) : Prop :=
  0 < c.numerator ∧ 0 < c.len ∧ c.numerator + c.len < M ∧ c.bound < M

def rAcc : Nat := 0
def rGood : Nat := 1
def rDen : Nat := 2
def rNum : Nat := 3
def rTerm : Nat := 4
def rSum : Nat := 5
def rNoWrap : Nat := 6
def rUnder : Nat := 7
def rPass : Nat := 8
def regCount : Nat := 9

def harmBody (c : Params) : List Instr :=
  [ .binop rDen .add .idx (.lit 1)
  , .binop rNum .add (.lit c.numerator) .idx
  , .binop rTerm .udiv (.reg rNum) (.reg rDen)
  , .binop rSum .add (.reg rAcc) (.reg rTerm)
  , .binop rNoWrap .ge (.reg rSum) (.reg rAcc)
  , .binop rUnder .le (.reg rSum) (.lit c.bound)
  , .binop rPass .mul (.reg rNoWrap) (.reg rUnder)
  , .binop rGood .mul (.reg rGood) (.reg rPass)
  , .mov rAcc (.reg rSum)
  ]

def harmProgram (c : Params) : Program := {
  regCount := regCount
  loopCount := c.len
  init := [.mov rGood (.lit 1)]
  body := harmBody c
  epilogue := []
  output := rGood
}

def term (c : Params) (i : Nat) : Nat := (c.numerator + i) / (i + 1)

def sourceSum (c : Params) : Nat :=
  (List.range c.len).foldl (fun acc i => acc + term c i) 0

@[ext] structure HState where
  acc : Nat
  good : Nat

def hstep (c : Params) (i : Nat) (x : HState) : HState :=
  let t := term c i
  let sum := (x.acc + t) % M
  let pass := (if x.acc ≤ sum then 1 else 0) * (if sum ≤ c.bound then 1 else 0)
  ⟨sum, (x.good * pass) % M⟩

def obs (s : RegState) : HState := ⟨s rAcc, s rGood⟩

def regStep (c : Params) (i : Nat) (s : RegState) : RegState :=
  let x := hstep c i (obs s)
  ((((((((s.set rDen (i + 1)).set rNum (c.numerator + i)).set rTerm (term c i)).set
    rSum x.acc).set rNoWrap (if s rAcc ≤ x.acc then 1 else 0)).set
    rUnder (if x.acc ≤ c.bound then 1 else 0)).set
    rPass (((if s rAcc ≤ x.acc then 1 else 0) *
      (if x.acc ≤ c.bound then 1 else 0)) % M)).set
    rGood x.good).set rAcc x.acc

theorem harmBody_denote (c : Params) (hc : c.Sane) (i : Nat) (hi : i < c.len)
    (s : RegState) :
    denoteInstrs i s (harmBody c) = some (regStep c i s) := by
  rcases hc with ⟨_, _, hnum, hbound⟩
  have hiM : i < M := by omega
  have hdenM : i + 1 < M := by omega
  have hden0 : i + 1 ≠ 0 := by omega
  have hnumM : c.numerator + i < M := by omega
  have htermM : (c.numerator + i) / (i + 1) < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnumM
  have hcnumM : c.numerator < M := by omega
  have hOneM : 1 < M := by decide
  simp only [harmBody, denoteInstrs, denoteInstr, denoteOperand]
  rw [Nat.mod_eq_of_lt hiM, Nat.mod_eq_of_lt hOneM,
    Nat.mod_eq_of_lt hcnumM, Nat.mod_eq_of_lt hbound]
  rw [denoteOp_add_of_lt hdenM]
  rw [denoteOp_add_of_lt hnumM]
  simp [denoteOp, regStep, obs, hstep, term, rAcc, rGood, rDen, rNum, rTerm,
    rSum, rNoWrap, rUnder, rPass, RegState.set, hden0,
    Nat.mod_eq_of_lt htermM]
  rfl

theorem harmProgram_wf (c : Params) : (harmProgram c).WF := by
  refine ⟨by simp [harmProgram, rGood, regCount], ?_, ?_, by simp [harmProgram]⟩
  · intro instr h
    simp only [harmProgram, List.mem_singleton] at h
    subst instr
    exact ⟨by simp [harmProgram, rGood, regCount], trivial⟩
  · intro instr h
    simp only [harmProgram, harmBody, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp +decide [harmProgram, Instr.WF, Operand.WF, regCount, rAcc, rGood, rDen, rNum,
        rTerm, rSum, rNoWrap, rUnder, rPass]

theorem harmProgram_denote (c : Params) (hc : c.Sane) :
    (harmProgram c).denote =
      some (((List.range c.len).foldl (fun x i => hstep c i x) ⟨0, 1⟩).good) := by
  refine Program.denote_eq_obs_foldl_mem (harmProgram c) (fun _ => True)
    (regStep c) obs (hstep c) HState.good
    (initialState.set rGood 1)
    (by simp [harmProgram, denoteInstrs, denoteInstr, denoteOperand, initialState,
      RegState.set, rGood, M]) trivial ?_ ?_ ?_ ?_
  · intro i s hi _
    exact harmBody_denote c hc i hi s
  · intros; trivial
  · intro i s _ _
    apply HState.ext <;> simp [regStep, obs, RegState.set, rAcc, rGood, rDen,
      rNum, rTerm, rSum, rNoWrap, rUnder, rPass]
  · intro s _
    rfl

private theorem hstep_good_le (c : Params) (i : Nat) (x : HState)
    (hx : x.good ≤ 1) : (hstep c i x).good ≤ x.good := by
  have hgM : x.good < M := Nat.lt_of_le_of_lt hx (by decide)
  by_cases h1 : x.acc ≤ (x.acc + term c i) % M <;>
    by_cases h2 : (x.acc + term c i) % M ≤ c.bound <;>
      simp [hstep, h1, h2, Nat.mod_eq_of_lt hgM]

private theorem fold_good_le (c : Params) (xs : List Nat) (x : HState)
    (hx : x.good ≤ 1) :
    (xs.foldl (fun x i => hstep c i x) x).good ≤ x.good := by
  induction xs generalizing x with
  | nil => simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hs := hstep_good_le c i x hx
      exact Nat.le_trans (ih _ (Nat.le_trans hs hx)) hs

private theorem no_wrap_of_ge {acc t : Nat} (hacc : acc < M) (ht : t < M)
    (hge : acc ≤ (acc + t) % M) : acc + t < M := by
  apply Nat.lt_of_not_ge
  intro hM
  have hsum : acc + t < M + M := by omega
  rw [Nat.mod_eq_sub_mod hM, Nat.mod_eq_of_lt (by omega : acc + t - M < M)] at hge
  omega

private theorem fold_accepts_sound (c : Params) (xs : List Nat)
    (hc : c.Sane) (acc : Nat) (hacc : acc ≤ c.bound) :
    let out := xs.foldl (fun x i => hstep c i x) ⟨acc, 1⟩
    out.good = 1 →
      out.acc = xs.foldl (fun a i => a + term c i) acc ∧ out.acc ≤ c.bound := by
  induction xs generalizing acc with
  | nil =>
      simp
      exact hacc
  | cons i xs ih =>
      simp only [List.foldl_cons]
      intro hout
      let y := hstep c i { acc := acc, good := 1 }
      have hy01 : y.good ≤ 1 := by
        exact hstep_good_le c i { acc := acc, good := 1 } (Nat.le_refl 1)
      have hyle :
          (xs.foldl (fun x i => hstep c i x) y).good ≤ y.good :=
        fold_good_le c xs y hy01
      have hyLower : 1 ≤ y.good := by
        rw [← hout]
        exact hyle
      have hy1 : y.good = 1 := Nat.le_antisymm hy01 hyLower
      simp only [y, hstep] at hy1
      have hprodmod :
          (if acc ≤ (acc + term c i) % M then 1 else 0) *
            (if (acc + term c i) % M ≤ c.bound then 1 else 0) % M = 1 := by
        simpa [M] using hy1
      have hprod :
          (if acc ≤ (acc + term c i) % M then 1 else 0) *
            (if (acc + term c i) % M ≤ c.bound then 1 else 0) = 1 := by
        have hpLt :
            (if acc ≤ (acc + term c i) % M then 1 else 0) *
              (if (acc + term c i) % M ≤ c.bound then 1 else 0) < M := by
          split <;> split <;> simp [M]
        rwa [Nat.mod_eq_of_lt hpLt] at hprodmod
      have hnowrap : acc ≤ (acc + term c i) % M := by
        by_cases hh : acc ≤ (acc + term c i) % M
        · exact hh
        · simp [hh] at hprod
      have hunder : (acc + term c i) % M ≤ c.bound := by
        by_cases hh : (acc + term c i) % M ≤ c.bound
        · exact hh
        · simp [hh] at hprod
      have hiN : i ≤ c.numerator * i := Nat.le_mul_of_pos_left i hc.1
      rw [Nat.mul_comm c.numerator i] at hiN
      have htermle : term c i ≤ c.numerator := by
        apply Nat.div_le_of_le_mul
        rw [Nat.add_mul]
        simp only [Nat.one_mul]
        omega
      have hnumLen := hc.2.2.1
      have hnumM0 : c.numerator < M := by omega
      have htM : term c i < M := Nat.lt_of_le_of_lt htermle hnumM0
      have hsumM : acc + term c i < M :=
        no_wrap_of_ge (Nat.lt_of_le_of_lt hacc hc.2.2.2) htM hnowrap
      have hyacc : y.acc = acc + term c i := by
        simp [y, hstep, Nat.mod_eq_of_lt hsumM]
      have hunder' : acc + term c i ≤ c.bound := by
        rwa [Nat.mod_eq_of_lt hsumM] at hunder
      have hybound : y.acc ≤ c.bound := by simpa [hyacc] using hunder'
      have hyEq : y = { acc := y.acc, good := 1 } := by
        apply HState.ext
        · rfl
        · exact hy1
      change (xs.foldl (fun x i => hstep c i x) y).good = 1 at hout
      rw [hyEq] at hout
      have hrest := ih y.acc hybound hout
      constructor
      · change (xs.foldl (fun x i => hstep c i x) y).acc = _
        rw [hyEq]
        simpa [hyacc] using hrest.1
      · change (xs.foldl (fun x i => hstep c i x) y).acc ≤ _
        rw [hyEq]
        exact hrest.2

theorem sourceAccepts_of_denote (c : Params) (hc : c.Sane)
    (h : (harmProgram c).denote = some 1) : sourceSum c ≤ c.bound := by
  rw [harmProgram_denote c hc] at h
  have hgood : ((List.range c.len).foldl
      (fun x i => hstep c i x) ⟨0, 1⟩).good = 1 := Option.some.inj h
  have hs := fold_accepts_sound c (List.range c.len) hc 0 (Nat.zero_le _) hgood
  unfold sourceSum
  rw [← hs.1]
  exact hs.2

def harmonicClaim (c : Params) (hc : c.Sane) :
  ProgramClaim (sourceSum c ≤ c.bound) where
  program := harmProgram c
  wellFormed := harmProgram_wf c
  acceptingValue := 1
  sound := sourceAccepts_of_denote c hc

end LeanCompCert.Ports.CeHarmonicFold

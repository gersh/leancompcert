import LeanCompCert.Ports.RamareCombined100MQuotient
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.BlockDefined

/-!
# Physical quotient/remainder transition for the Ramaré sweep

This is the straight-line `u64` realization of `PsiQR.advance`.  The source
transition has two arithmetic branches; the CompCert fragment is deliberately
branch-free.  It evaluates both candidates and selects with a `0`/`1` gate.
Only the selected branch is required not to wrap, so inactive scratch values
may be arbitrary machine words.

The input/output convention is fixed so the block can be reused twice in the
eventual combined checker by moving each psi endpoint through the same work
registers:

* `0`: quotient (updated in place);
* `1`: remainder (updated in place);
* `2`: lambda increment;
* `3`: current denominator `n`.

Registers `4` through `20` are scratch.
-/

namespace LeanCompCert.Ports.RamareCombined100M.PsiQRBlock

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

def rq : Nat := 0
def rr : Nat := 1
def rlam : Nat := 2
def rn : Nat := 3

def body : List Instr :=
  [ .binop 4 .add (.reg rr) (.reg rlam)       -- a = r + lambda
  , .binop 5 .add (.reg rn) (.lit 1)          -- d = n + 1
  , .binop 6 .le (.reg rq) (.reg 4)           -- positive-branch gate
  , .binop 7 .sub (.reg 4) (.reg rq)
  , .binop 8 .udiv (.reg 7) (.reg 5)
  , .binop 9 .urem (.reg 7) (.reg 5)
  , .binop 10 .sub (.reg rq) (.reg 4)
  , .binop 11 .udiv (.reg 10) (.reg 5)
  , .binop 12 .urem (.reg 10) (.reg 5)
  , .binop 13 .ne (.reg 12) (.lit 0)
  , .binop 14 .add (.reg rq) (.reg 8)
  , .binop 15 .sub (.reg rq) (.reg 11)
  , .binop 15 .sub (.reg 15) (.reg 13)
  , .binop 16 .sub (.reg 5) (.reg 12)
  , .binop 16 .mul (.reg 16) (.reg 13)
  , .binop 17 .sub (.lit 1) (.reg 6)
  , .binop 18 .mul (.reg 14) (.reg 6)
  , .binop 19 .mul (.reg 15) (.reg 17)
  , .binop rq .add (.reg 18) (.reg 19)
  , .binop 18 .mul (.reg 9) (.reg 6)
  , .binop 19 .mul (.reg 16) (.reg 17)
  , .binop rr .add (.reg 18) (.reg 19) ]

/-- The only partial operations divide by `n+1`, which is nonzero under the
machine-width loop invariant. -/
theorem body_defined (k : Nat) (s : RegState) (hn : s rn + 1 < M) :
    SAllDefined k s body := by
  have hdM : (s rn + 1) % M = s rn + 1 := Nat.mod_eq_of_lt hn
  have hd0 : (s rn + 1) % M ≠ 0 := by rw [hdM]; omega
  simp [body, SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rq, rr, rlam, rn, show (s 3 + 1) % M ≠ 0 by simpa [rn] using hd0]

/-- Literal word-level result computed by `body`.  Keeping this formula
separate prevents the compiler proof from repeatedly normalizing the complete
register-update nest while reasoning about the source arithmetic. -/
def wordAdvance (n lam : Nat) (z : PsiQR) : PsiQR :=
  let a := (z.r + lam) % M
  let d := (n + 1) % M
  let g := if z.q ≤ a then 1 else 0
  let tp := (a + (M - z.q)) % M
  let kp := (tp / d) % M
  let rp := (tp % d) % M
  let tn := (z.q + (M - a)) % M
  let kn := (tn / d) % M
  let u := (tn % d) % M
  let unz := if u ≠ 0 then 1 else 0
  let qpos := (z.q + kp) % M
  let qneg := ((z.q + (M - kn)) % M + (M - unz)) % M
  let rneg := ((d + (M - u)) % M * unz) % M
  let ng := (1 + (M - g)) % M
  ⟨((qpos * g) % M + (qneg * ng) % M) % M,
    ((rp * g) % M + (rneg * ng) % M) % M⟩

set_option maxHeartbeats 1000000 in
/-- Evaluation of the fixed instruction sequence is definitionally the
word-level formula above. -/
theorem body_run (k : Nat) (s : RegState) (hd : (s rn + 1) % M ≠ 0) :
    let f := srun k s body
    f rq = (wordAdvance (s rn) (s rlam) ⟨s rq, s rr⟩).q ∧
      f rr = (wordAdvance (s rn) (s rlam) ⟨s rq, s rr⟩).r := by
  change (s 3 + 1) % M ≠ 0 at hd
  simp [body, wordAdvance, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rq, rr, rlam, rn, hd]
  constructor <;>
    by_cases hu :
      (s 0 + (M - (s 1 + s 2) % M)) % M % ((s 3 + 1) % M) % M = 0 <;>
      by_cases hg : s 0 ≤ (s 1 + s 2) % M <;>
      simp [hu, hg]

/-- Under the explicit word bounds, the branchless word formula is the exact
source quotient/remainder transition. -/
theorem wordAdvance_eq (n lam : Nat) (z : PsiQR)
    (hq : z.q < M) (_hr : z.r < M) (_hlam : lam < M)
    (hn : n + 1 < M) (ha : z.r + lam < M)
    (houtQ : (z.advance n lam).q < M) :
    wordAdvance n lam z = z.advance n lam := by
  have hd : 0 < n + 1 := by omega
  have hdM : (n + 1) % M = n + 1 := Nat.mod_eq_of_lt hn
  have haM : (z.r + lam) % M = z.r + lam := Nat.mod_eq_of_lt ha
  have hzeroGate : (1 + (M - 1)) % M = 0 := by decide
  have subExact : ∀ {a b : Nat}, b ≤ a → a < M →
      (a + (M - b)) % M = a - b := by
    intro a b hba haM'
    exact Option.some.inj (LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le hba haM')
  unfold wordAdvance
  simp only [hdM, haM]
  by_cases h : z.q ≤ z.r + lam
  · have hsub : (z.r + lam + (M - z.q)) % M = z.r + lam - z.q := by
      exact subExact h ha
    have htpM : z.r + lam - z.q < M := by omega
    have hkpM : (z.r + lam - z.q) / (n + 1) < M :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) htpM
    have hrM : (z.r + lam - z.q) % (n + 1) < M :=
      Nat.lt_trans (Nat.mod_lt _ hd) hn
    have hqout : z.q + (z.r + lam - z.q) / (n + 1) < M := by
      simpa [PsiQR.advance, h] using houtQ
    simp [h, hsub, hzeroGate, PsiQR.advance, Nat.mod_eq_of_lt hkpM,
      Nat.mod_eq_of_lt hrM, Nat.mod_eq_of_lt hqout]
  · have hlt : z.r + lam < z.q := by omega
    have hsub : (z.q + (M - (z.r + lam))) % M = z.q - (z.r + lam) := by
      exact subExact (Nat.le_of_lt hlt) hq
    let t := z.q - (z.r + lam)
    have htpos : 0 < t := by simp [t]; omega
    have htM : t < M := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hq
    have hkle : t / (n + 1) ≤ t := Nat.div_le_self _ _
    have hkM : t / (n + 1) < M := Nat.lt_of_le_of_lt hkle htM
    have huM : t % (n + 1) < M :=
      Nat.lt_trans (Nat.mod_lt _ hd) hn
    by_cases hz : t % (n + 1) = 0
    · have hkq : t / (n + 1) ≤ z.q := by
        exact Nat.le_trans hkle (Nat.sub_le _ _)
      have hq1 : (z.q + (M - t / (n + 1))) % M =
          z.q - t / (n + 1) := by
        exact subExact hkq hq
      have hqresM : z.q - t / (n + 1) < M :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) hq
      simp [h, hsub, t, hz, hq1, PsiQR.advance,
        Nat.mod_eq_of_lt hkM,
        Nat.mod_eq_of_lt hqresM]
    · have hu : 0 < t % (n + 1) := Nat.pos_of_ne_zero hz
      have hult : t % (n + 1) < n + 1 := Nat.mod_lt _ hd
      have hdTwo : 1 < n + 1 := by omega
      have hklt : t / (n + 1) < t := Nat.div_lt_self htpos hdTwo
      have hk1q : t / (n + 1) + 1 ≤ z.q := by
        simp only [t] at hklt ⊢
        omega
      have hq1 : (z.q + (M - t / (n + 1))) % M =
          z.q - t / (n + 1) := by
        exact subExact (by omega) hq
      have hq2 : (z.q - t / (n + 1) + (M - 1)) % M =
          z.q - t / (n + 1) - 1 := by
        exact subExact (by omega) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hq)
      have hr1 : (n + 1 + (M - t % (n + 1))) % M =
          n + 1 - t % (n + 1) := by
        exact subExact (Nat.le_of_lt hult) hn
      have hqout : z.q - t / (n + 1) - 1 < M := by
        exact Nat.lt_of_le_of_lt
          (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) hq
      have hrout : n + 1 - t % (n + 1) < M := by omega
      simp [h, hsub, t, hz, hq1, hq2, hr1, PsiQR.advance,
        Nat.mod_eq_of_lt hkM, Nat.mod_eq_of_lt huM,
        Nat.mod_eq_of_lt hqout, Nat.mod_eq_of_lt hrout]

/-- The branchless block implements the exact mathematical transition whenever
the live inputs and selected output fit in one word. -/
theorem body_spec (k : Nat) (s : RegState)
    (hq : s rq < M) (hr : s rr < M) (hlam : s rlam < M)
    (hn : s rn + 1 < M) (ha : s rr + s rlam < M)
    (houtQ : (PsiQR.advance (s rn) (s rlam) ⟨s rq, s rr⟩).q < M) :
    let f := srun k s body
    f rq = (PsiQR.advance (s rn) (s rlam) ⟨s rq, s rr⟩).q ∧
      f rr = (PsiQR.advance (s rn) (s rlam) ⟨s rq, s rr⟩).r := by
  have hd0 : (s rn + 1) % M ≠ 0 := by
    rw [Nat.mod_eq_of_lt hn]
    omega
  have hrun := body_run k s hd0
  rw [wordAdvance_eq (s rn) (s rlam) ⟨s rq, s rr⟩ hq hr hlam hn ha houtQ]
    at hrun
  exact hrun

/-- The partial register denotation reaches the same state described by
`body_spec`; this is the form used by a surrounding `Program` proof. -/
theorem body_denote (k : Nat) (s : RegState)
    (hq : s rq < M) (hr : s rr < M) (hlam : s rlam < M)
    (hn : s rn + 1 < M) (ha : s rr + s rlam < M)
    (houtQ : (PsiQR.advance (s rn) (s rlam) ⟨s rq, s rr⟩).q < M) :
    ∃ s', denoteInstrs k s body = some s' ∧
      s' rq = (PsiQR.advance (s rn) (s rlam) ⟨s rq, s rr⟩).q ∧
      s' rr = (PsiQR.advance (s rn) (s rlam) ⟨s rq, s rr⟩).r := by
  refine ⟨srun k s body, denoteInstrs_eq_srun k body s (body_defined k s hn), ?_⟩
  exact body_spec k s hq hr hlam hn ha houtQ

/-! ## Standalone compiler package

This one-step wrapper is both a regression target and the compiler theorem
used when embedding the block in a larger program.  The production checker
will execute the same `body` twice per candidate after moving each endpoint
through registers `0`--`3`.
-/

def regCount : Nat := 21

def program (q r lam n output : Nat) : Program := {
  regCount := regCount
  loopCount := 1
  init :=
    [ .mov rq (.lit q)
    , .mov rr (.lit r)
    , .mov rlam (.lit lam)
    , .mov rn (.lit n) ]
  body := body
  epilogue := []
  output := output
}

theorem program_wf (q r lam n output : Nat) (hout : output < regCount) :
    (program q r lam n output).WF := by
  simpa [Program.WF, Instr.WF, Operand.WF, program, body, regCount,
    rq, rr, rlam, rn] using hout

/-- Generated CCIR, and therefore emitted C through the verified backend,
computes exactly the packaged register denotation. -/
theorem program_compiled (q r lam n output : Nat) (hout : output < regCount) :
    ((evalCCSequence LeanCompCert.Verified.emptyCCEnv
        (program q r lam n output).compile).bind
      (fun env => env ⟨(program q r lam n output).output + 1⟩)) =
      (program q r lam n output).denote.map (fun x => (x : Int)) :=
  Program.evalCC_compile _ (program_wf q r lam n output hout)

end LeanCompCert.Ports.RamareCombined100M.PsiQRBlock

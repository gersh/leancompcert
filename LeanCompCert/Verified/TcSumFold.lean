/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.TwosComplementFold
import LeanCompCert.Verified.InstrBlock

/-!
# The accumulator loop denotes `tcSum`

The scan certificates' machine side replays `A = tcVal (tcSum ps)` in the
kernel.  This module closes the other arrow: an emitted `Program` whose loop
adds a per-index term into one register **is** `tcSum` of the recorded list —
so the word a compiled run reports as `A` is definitionally the word the
checker refolds.

Both sides reduce to a single plain sum:

* `tcSum` right-folds `(t + acc) % 2⁶⁴`; collapsing the nested reductions
  gives `(Σ tᵢ) % 2⁶⁴`.
* The machine loop left-folds `(acc + t) % 2⁶⁴`; same collapse, same sum.

⚠ The recorded list and the loop traverse the terms in opposite orders; the
sum normal form is what makes the orientation irrelevant, with no appeal to
commutativity of the *modular* operation.
-/

namespace LeanCompCert.Verified.TcSumFold

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.FoldBridge
open LeanCompCert.Verified.MulWide
open LeanCompCert.Verified.TwosComplementFold

theorem M_eq_B64 : M = B64 := rfl

/-- `tcSum` is the plain sum of the computed words, reduced once. -/
theorem tcSum_eq_sum_mod : ∀ ps : List (Nat × Int),
    tcSum ps = (ps.map Prod.fst).sum % B64
  | [] => by simp [tcSum]
  | p :: ps => by
      rw [tcSum, tcSum_eq_sum_mod ps, List.map_cons, List.sum_cons]
      have hB : B64 = 18446744073709551616 := rfl
      rw [hB]
      omega

/-- The machine's left fold is the same sum, reduced once. -/
theorem foldl_add_mod (f : Nat → Nat) : ∀ n : Nat,
    (List.range n).foldl (fun acc i => (acc + f i) % M) 0
      = ((List.range n).map f).sum % M
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.foldl_append, List.map_append,
        List.sum_append, foldl_add_mod f n]
      simp only [List.foldl_cons, List.foldl_nil, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil]
      have hM : M = 18446744073709551616 := rfl
      rw [hM]
      omega

/-- **An accumulator program denotes `tcSum` of the recorded list.**

`hps` is the binding between the certificate data and the loop: the recorded
computed words are exactly the per-index terms.  Everything else is the
`denote_eq_scalar_foldl` obligations — a body simulation, an invariant, and
the accumulator observation. -/
theorem Program.denote_eq_tcSum
    (p : Program) (P : RegState → Prop) (step : Nat → RegState → RegState)
    (f : Nat → Nat) (ps : List (Nat × Int)) (s₀ : RegState)
    (hps : ps.map Prod.fst = (List.range p.loopCount).map f)
    (hInit : denoteInstrs 0 initialState p.init = some s₀)
    (hP₀ : P s₀) (hAcc : s₀ p.output = 0)
    (hEpilogueNil : p.epilogue = [])
    (hStep : ∀ index s, P s → denoteInstrs index s p.body = some (step index s))
    (hClosed : ∀ index s, P s → P (step index s))
    (hObs : ∀ index s, P s →
      (step index s) p.output = (s p.output + f index) % M) :
    p.denote = some (tcSum ps) := by
  have h := FoldBridge.Program.denote_eq_scalar_foldl p P step
    (fun index acc => (acc + f index) % M) s₀ 0 hInit hP₀ hAcc hEpilogueNil
    hStep hClosed hObs
  rw [h, foldl_add_mod, tcSum_eq_sum_mod, hps, M_eq_B64]

/-- Sanity: the one-register index-summing program is `tcSum` of the recorded
index list — at every size, with no per-size proof work. -/
example (n : Nat) (e : Nat → Int) :
    (Program.mk 1 n [] [.binop 0 .add (.reg 0) .idx] [] 0).denote
      = some (tcSum ((List.range n).map (fun i => (i % M, e i)))) := by
  refine Program.denote_eq_tcSum _ (fun _ => True)
    (fun index s => s.set 0 ((s 0 + index % M) % M))
    (fun i => i % M) _ initialState ?_ rfl trivial rfl rfl
    (fun index s _ => rfl) (fun _ _ _ => trivial)
    (fun index s _ => rfl)
  rw [List.map_map]
  rfl

/-! ## The accumulator loop, with the term block abstracted

The shape every scan sample has: a straight-line **term block** writes the
index's term into `tr`, then one add folds it into `acc`.  The term block is
the whole evaluator (trig, complex product, …); nothing here depends on what
it is, only on what it **owes** — packaged as `TermSpec` so a concrete block
discharges four facts and inherits the denotation.

⚠ The obligations are guarded by `index < n`: a real term block is only
meaningful below the sample count (its fixed-point products overflow beyond
it), and demanding it for every index would make the contract unmeetable. -/

open LeanCompCert.Verified.InstrBlock

/-- Loop body: the term block, then the accumulate. -/
def accumBody (termBody : List Instr) (acc tr : Nat) : List Instr :=
  termBody ++ [.binop acc .add (.reg acc) (.reg tr)]

/-- The accumulator program.  Output is the accumulator; no epilogue. -/
def accumProgram (regCount n : Nat) (init termBody : List Instr)
    (acc tr : Nat) : Program :=
  { regCount := regCount, loopCount := n, init := init
  , body := accumBody termBody acc tr, epilogue := [], output := acc }

/-- **What a term block owes.**  Under the invariant `P`, at every index below
`n`: it is division-free, keeps `P`, lands `f index` in `tr`, and leaves the
accumulator alone; and `P` is blind to the accumulator. -/
structure TermSpec (termBody : List Instr) (P : RegState → Prop)
    (f : Nat → Nat) (acc tr n : Nat) : Prop where
  noDiv : ∀ i ∈ termBody, NoDivI i = true
  preserved : ∀ index s, index < n → P s → P (srun index s termBody)
  term : ∀ index s, index < n → P s → srun index s termBody tr = f index
  accKept : ∀ index s, index < n → P s → srun index s termBody acc = s acc
  accFree : ∀ s v, P s → v < M → P (s.set acc v)

theorem noDiv_accumBody {termBody : List Instr} {acc tr : Nat}
    (h : ∀ i ∈ termBody, NoDivI i = true) :
    ∀ i ∈ accumBody termBody acc tr, NoDivI i = true := by
  intro i hi
  unfold accumBody at hi
  rcases List.mem_append.mp hi with h1 | h1
  · exact h i h1
  · simp only [List.mem_singleton] at h1
    subst h1
    rfl

/-- **The accumulator loop denotes `tcSum` of the recorded list.**  The
binding to the certificate is `hps`: the recorded computed words are the
per-index terms. -/
theorem accumProgram_denote_tcSum {regCount n : Nat} {init termBody : List Instr}
    {acc tr : Nat} {P : RegState → Prop} {f : Nat → Nat}
    (spec : TermSpec termBody P f acc tr n)
    (ps : List (Nat × Int)) (hps : ps.map Prod.fst = (List.range n).map f)
    (s₀ : RegState) (hInit : denoteInstrs 0 initialState init = some s₀)
    (hP₀ : P s₀) (hAcc : s₀ acc = 0) :
    (accumProgram regCount n init termBody acc tr).denote = some (tcSum ps) := by
  have hbody := srun_correct (l := accumBody termBody acc tr)
  have h := FoldBridge.Program.denote_eq_obs_foldl_mem
    (accumProgram regCount n init termBody acc tr) P
    (fun index s => (srun index s termBody).set acc ((s acc + f index) % M))
    (fun s => s acc) (fun index a => (a + f index) % M) id s₀ hInit hP₀
    (by
      intro index s hidx hP
      show denoteInstrs index s (accumBody termBody acc tr) = _
      rw [hbody index (noDiv_accumBody spec.noDiv) s]
      unfold accumBody
      rw [srun_append, srun_cons, srun_nil]
      simp only [sdest, sval, denoteOperand, denoteOp, Option.getD_some]
      rw [spec.term index s hidx hP, spec.accKept index s hidx hP])
    (by
      intro index s hidx hP
      exact spec.accFree _ _ (spec.preserved index s hidx hP)
        (Nat.mod_lt _ (by decide)))
    (by
      intro index s _ _
      simp [RegState.set])
    (by
      intro s _
      rfl)
  rw [h]
  show some ((List.range n).foldl (fun a index => (a + f index) % M) (s₀ acc))
    = some (tcSum ps)
  rw [hAcc, foldl_add_mod, tcSum_eq_sum_mod, hps, M_eq_B64]

/-- Sanity: the term block `tr := idx`, no invariant, at every size. -/
example (n : Nat) (e : Nat → Int) :
    (accumProgram 2 n [] [.mov 1 .idx] 0 1).denote
      = some (tcSum ((List.range n).map (fun i => (i % M, e i)))) := by
  refine accumProgram_denote_tcSum (P := fun _ => True) (f := fun i => i % M)
    ⟨?_, fun _ _ _ _ => trivial, ?_, ?_, fun _ _ _ _ => trivial⟩
    _ ?_ initialState rfl trivial rfl
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    rfl
  · intro index s _ _
    rfl
  · intro index s _ _
    rfl
  · rw [List.map_map]
    rfl

#print axioms Program.denote_eq_tcSum
#print axioms accumProgram_denote_tcSum

end LeanCompCert.Verified.TcSumFold

import LeanCompCert.Ports.MobiusResidueRealisation
import LeanCompCert.Ports.MobiusResidueAcc
import LeanCompCert.Ports.MobiusResidueTest

/-!
# One window of the per-integer `Σ μ(m)/m` residue

`MobiusResidueRealisation` shows the `mobiusLiveResidue` block denotes
`resStep`.  `MobiusResidueWeight`, `MobiusResidueAcc` and `MobiusResidueTest`
show that each section of `resStep` is the arithmetic it claims to be.  This
file supplies the two things the window-level statement needs on top of those:

* `accTrue_close` — the **accumulated** round-to-nearest error over `[1, n]`.
  The fixed-point accumulator tracks `2^(63+k)` times the exact rational
  partial sum to within `n/2` ulps, cleared of denominators.  This is the
  hypothesis `happ` of `MobiusResidueTest.sound_of_test`, and it is what makes
  a passing integer test a bound on the *real* sum rather than on its
  fixed-point image.
* `coreBody_regDests_disjoint` / `coreInit_regDests_disjoint` — **the two
  halves of the loop body do not interact.**  Every register the sieve core
  writes lies outside `{100,…,104} ∪ {150,…,171}`, and (by
  `mobiusLiveResidue_denote`) the residue writes nothing else.  So the
  residue's five accumulators are a function of the four signals in registers
  `65`, `79`, `80`, `133` alone, and bolting a residue onto the core cannot
  perturb the sieve.

Together with `sound_of_test` these give, at a single gated integer `n` whose
carry-in really is the accumulator at `n − 1`,

```
4 · (n+1) · (Σ_{m ≤ n} μ(m)·(D/m))² ≤ D²   for every common denominator D,
```

which is `|Σ_{m ≤ n} μ(m)/m| ≤ 1/(2·√(n+1))` with the denominators cleared,
i.e. `MathExtras.Reductions.PlattStrongerRangeNatFamily` at `n`.

Nothing here assumes anything about the sieve: `mu` is an arbitrary function
into `{−1, 0, 1}` and the signals are the ones a correct sieve would present.
Supplying that the sieve *does* present them is the one remaining premise.

**Not proved here** (and not assumed anywhere either — it is simply absent):
the induction that chains `ResInv` across a whole window, i.e. that a zero
violation count at the *end* of the loop forces the per-step hypotheses at
*every* integer of the window.  The per-step content is complete; what is
missing is the routine `List.foldl` induction over `resFold`, together with the
proof that the sieve core emits `muSig mu n` at the gated iterations.
-/

namespace LeanCompCert.Ports.MobiusResidueRealisation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

/-! ## The window model -/

/-- Iterating the model over a list of signals. -/
def resFold (k : Nat) : List Sig → Res → Res
  | [], r => r
  | g :: gs, r => resFold k gs (resStep k g r)

/-- The signal a gated integer `n` presents: `n` in register `65`, the two
`μ` indicators in `79`/`80`, the main-accumulation gate set. -/
def muSig (mu : Nat → Int) (n : Nat) : Sig :=
  ⟨n, if mu n = 1 then 1 else 0, if mu n = -1 then 1 else 0, 1⟩

/-- The exact fixed-point accumulator `Σ_{m ≤ n} μ(m)·round(2^(63+k)/m)`. -/
def accTrue (k : Nat) (mu : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => accTrue k mu n + mu (n + 1) * (wgt k (n + 1) : Int)

/-- `Σ_{m ≤ n} μ(m)·(D/m)`: the exact partial sum over a common denominator
`D`.  For `D` divisible by every `m ≤ n` this is `D · Σ_{m ≤ n} μ(m)/m`. -/
def numTrue (mu : Nat → Int) (D : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => numTrue mu D n + mu (n + 1) * ((D / (n + 1) : Nat) : Int)

/-- The invariant the residue's five registers carry from one gated integer to
the next. -/
structure ResInv (k : Nat) (mu : Nat → Int) (n : Nat) (r : Res) : Prop where
  loLt : r.tLo < M
  hiLt : r.tHi < M
  acc : (r.tLo : Int) + (M : Int) * r.tHi = 2 ^ (64 + k) + accTrue k mu n
  bnd : (accTrue k mu n).natAbs ≤ 2 ^ (62 + k)
  cel : CeilInv r.cel (n + 1)
  celSq : r.celSq = r.cel * r.cel
  celLt : r.cel + 1 < 2 ^ 32


/-! ## The rounding budget, summed over the window -/

private theorem mu_natAbs_le_one {mu : Nat → Int}
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0) (m : Nat) :
    (mu m).natAbs ≤ 1 := by
  rcases hmu m with h | h | h <;> rw [h] <;> decide

/-- **The accumulated round-to-nearest error.**  The fixed-point accumulator
tracks `2^(63+k)` times the exact partial sum to within half an ulp per term.
Everything is cleared of denominators: `D` is any common multiple of
`1, …, n`.  This is what makes a passing integer test a bound on the *real*
sum rather than on its fixed-point image. -/
theorem accTrue_close (k : Nat) (mu : Nat → Int)
    (hmu : ∀ m, mu m = 1 ∨ mu m = -1 ∨ mu m = 0) (D : Nat) :
    ∀ n : Nat, (∀ m, 1 ≤ m → m ≤ n → m ∣ D) →
      2 * (accTrue k mu n * D - 2 ^ (63 + k) * numTrue mu D n).natAbs
        ≤ n * D := by
  intro n
  induction n with
  | zero => intro _; simp [accTrue, numTrue]
  | succ n ih =>
      intro hdvd
      have hIH := ih (fun m h1 h2 => hdvd m h1 (Nat.le_succ_of_le h2))
      obtain ⟨e, he⟩ := hdvd (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
        (Nat.le_refl _)
      have hDe : (D : Int) = ((n : Int) + 1) * (e : Int) := by
        rw [he]; push_cast; grind
      have hDdiv : ((D / (n + 1) : Nat) : Int) = (e : Int) := by
        rw [he, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]
      obtain ⟨hup, hdown⟩ :=
        wgt_close k (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      have hpush : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by push_cast; grind
      rw [hpush] at hup hdown
      -- the per-term error, cleared of denominators
      have hbase :
          2 * ((wgt k (n + 1) : Int) * ((n : Int) + 1) - 2 ^ (63 + k)).natAbs
            ≤ n + 1 := by omega
      have hterm :
          2 * (mu (n + 1) * ((wgt k (n + 1) : Int) * D
                - 2 ^ (63 + k) * ((D / (n + 1) : Nat) : Int))).natAbs ≤ D := by
        have hfac : (wgt k (n + 1) : Int) * D
            - 2 ^ (63 + k) * ((D / (n + 1) : Nat) : Int)
            = (e : Int) * ((wgt k (n + 1) : Int) * ((n : Int) + 1)
                - 2 ^ (63 + k)) := by
          rw [hDe, hDdiv]; grind
        rw [hfac, Int.natAbs_mul, Int.natAbs_mul]
        have hmul := mu_natAbs_le_one hmu (n + 1)
        have hee : (e : Int).natAbs = e := Int.natAbs_natCast e
        rw [hee]
        have hD' : D = (n + 1) * e := he
        calc 2 * ((mu (n + 1)).natAbs *
              (e * ((wgt k (n + 1) : Int) * ((n : Int) + 1)
                - 2 ^ (63 + k)).natAbs))
            ≤ 2 * (1 *
              (e * ((wgt k (n + 1) : Int) * ((n : Int) + 1)
                - 2 ^ (63 + k)).natAbs)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hmul)
          _ = e * (2 * ((wgt k (n + 1) : Int) * ((n : Int) + 1)
                - 2 ^ (63 + k)).natAbs) := by grind
          _ ≤ e * (n + 1) := Nat.mul_le_mul_left e hbase
          _ = D := by rw [hD']; exact Nat.mul_comm _ _
      have hsplit :
          accTrue k mu (n + 1) * D - 2 ^ (63 + k) * numTrue mu D (n + 1)
            = (accTrue k mu n * D - 2 ^ (63 + k) * numTrue mu D n)
              + mu (n + 1) * ((wgt k (n + 1) : Int) * D
                  - 2 ^ (63 + k) * ((D / (n + 1) : Nat) : Int)) := by
        simp only [accTrue, numTrue]; grind
      rw [hsplit]
      have htri := Int.natAbs_add_le
        (accTrue k mu n * D - 2 ^ (63 + k) * numTrue mu D n)
        (mu (n + 1) * ((wgt k (n + 1) : Int) * D
          - 2 ^ (63 + k) * ((D / (n + 1) : Nat) : Int)))
      have hexp : (n + 1) * D = n * D + D := by grind
      omega


/-! ## Non-interference: the sieve core never touches the residue's registers -/

/-- The register an instruction writes, if any.  A `store` writes only the
array. -/
def ainstrRegDest? : AInstr → Option Nat
  | .scalar (.mov d _) => some d
  | .scalar (.binop d _ _ _) => some d
  | .load d _ => some d
  | .store _ _ => none

/-- `S` covers every register destination of a block. -/
def RegDestsIn (S : Nat → Bool) (l : List AInstr) : Prop :=
  l.all (fun a => match ainstrRegDest? a with
    | some d => S d
    | none => true) = true

private theorem denoteAInstr_reg_frame {len idx : Nat} {s s' : AState}
    {a : AInstr} (h : denoteAInstr len idx s a = some s') {j : Nat}
    (hj : ainstrRegDest? a ≠ some j) : s'.regs j = s.regs j := by
  cases a with
  | scalar i =>
      cases i with
      | mov d src =>
          simp only [denoteAInstr, denoteInstr, Option.bind_eq_bind,
            Option.bind_some, Option.some.injEq] at h
          subst h
          simp only [ainstrRegDest?, ne_eq, Option.some.injEq] at hj
          simp only [RegState.set]
          exact if_neg (fun h => hj h.symm)
      | binop d op l r =>
          simp only [denoteAInstr, denoteInstr, Option.bind_eq_bind] at h
          cases hv : denoteOp op (denoteOperand idx s.regs l)
              (denoteOperand idx s.regs r) with
          | none => rw [hv] at h; exact absurd h (by simp)
          | some v =>
              rw [hv] at h
              simp only [Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              simp only [ainstrRegDest?, ne_eq, Option.some.injEq] at hj
              simp only [RegState.set]
              exact if_neg (fun h => hj h.symm)
  | load d i =>
      obtain ⟨_, _, _, hframe⟩ := denoteAInstr_load_some h
      simp only [ainstrRegDest?, ne_eq, Option.some.injEq] at hj
      exact hframe j (fun h => hj h.symm)
  | store i sr =>
      obtain ⟨_, hregs, _, _⟩ := denoteAInstr_store_some h
      rw [hregs]

/-- **Register frame.**  A block leaves every register outside its destination
set untouched — `load` and `store` included. -/
theorem denoteAInstrs_reg_frame (len idx : Nat) (S : Nat → Bool) :
    ∀ (l : List AInstr), RegDestsIn S l → ∀ (s s' : AState),
      denoteAInstrs len idx s l = some s' →
      ∀ j, S j = false → s'.regs j = s.regs j := by
  intro l
  induction l with
  | nil =>
      intro _ s s' h j _
      simp only [denoteAInstrs, Option.some.injEq] at h
      exact h ▸ rfl
  | cons a l ih =>
      intro hall s s' h j hj
      have hd : (match ainstrRegDest? a with
          | some d => S d | none => true) = true :=
        (List.all_eq_true.mp hall) a (by simp)
      have hrest : RegDestsIn S l := by
        refine List.all_eq_true.mpr ?_
        intro x hx
        exact (List.all_eq_true.mp hall) x (List.mem_cons_of_mem _ hx)
      simp only [denoteAInstrs, Option.bind_eq_bind] at h
      cases hstep : denoteAInstr len idx s a with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hstep] at h
          simp only [Option.bind_some] at h
          have hne : ainstrRegDest? a ≠ some j := by
            intro hEq
            rw [hEq] at hd
            simp only at hd
            rw [hj] at hd
            exact absurd hd (by simp)
          rw [ih hrest s1 s' h j hj]
          exact denoteAInstr_reg_frame hstep hne

/-- The residue's own register file. -/
def ResidueRegs (j : Nat) : Bool :=
  decide ((100 ≤ j ∧ j ≤ 104) ∨ (150 ≤ j ∧ j ≤ 171))

/-- **Non-interference.**  Every register the sieve core writes lies outside
the residue's register file.  Together with `mobiusLiveResidue_denote` — which
says the residue writes nothing else — the two halves of the loop body are
independent: the residue's five accumulators are a function of the four
signals `65`, `79`, `80`, `133` alone, and the sieve's state is unaffected by
which residue is bolted on. -/
theorem coreBody_regDests_disjoint (c : Cfg) :
    RegDestsIn (fun j => !ResidueRegs j) c.coreBody := rfl

/-- The same for the core's initialization block. -/
theorem coreInit_regDests_disjoint (c : Cfg) :
    RegDestsIn (fun j => !ResidueRegs j) c.coreInit := by
  refine List.all_eq_true.mpr ?_
  intro x hx
  simp only [Cfg.coreInit, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ⟨y, _, hy⟩ | h
  · rcases hy with h | h | h <;> subst h <;> rfl
  · rcases h with h | h | h | h | h <;> subst h <;> rfl

end LeanCompCert.Ports.MobiusResidueRealisation

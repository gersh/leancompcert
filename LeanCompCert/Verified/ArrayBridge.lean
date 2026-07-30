import LeanCompCert.Verified.ArrayState
import LeanCompCert.Verified.MemFragment
import LeanCompCert.Verified.Package

/-!
# M6 — the array bridge: `AProgram` → CCIR → generated C

`Verified.ArrayState` gives a register machine with one array and a
denotation (`AProgram.denote`); `Verified.MemFragment` gives CCIR
`.load`/`.store` with a proved lowering into the generated-C model.  Nothing
joined them: `Reflect.Program` has `Program.compile`/`Program.evalCC_compile`
and `ListFold.LProgram` has its analogue, but `AProgram` had neither.

This file is that join.

## The memory layout

The array is one `uint64_t[]` whose base address arrives as a **function
parameter** (`baseDecl`, a `u64`).  Cell `n` lives at byte address
`8·n + base`, computed per access by

```
  addr = idx * 8            -- u64
  addr = addr + base        -- u64
  cell = (uint64_t *) addr  -- the address materialization
```

and then read or written by the CCIR `.load`/`.store` of `MemFragment`, which
is where the proved lowering takes over.  The materialization is an ordinary
`StraightInstruction.cast` at a pointer type; it is value-preserving because
`Proof.bitWidth`/`Proof.ccBitWidth` model pointers as 64-bit machine words.
No new CCIR construct, no new C statement shape and no relaxation of either
validator is needed: the emitted C is `(*_local_k) = _local_j;` with
`_local_k` declared `uint64_t *`, which both `CCIR.validateProgram` and
`C.validateTranslationUnit` already accept under the `portable` profile.

Local numbering extends `Reflect`'s: `⟨0⟩` is the `u8` comparison scratch,
`⟨i+1⟩` is register `i`, and the three array locals sit above the registers —
`⟨regCount+1⟩` the byte address, `⟨regCount+2⟩` the cell pointer,
`⟨regCount+3⟩` the base parameter.  So every scalar instruction compiles
through `Reflect.compileInstr` **verbatim** and every scalar simulation lemma
of `Reflect` is reused as-is.

## What the bridge theorem says, and what it does not

`AProgram.evalCC_compile` is the analogue of `Program.evalCC_compile`: the
compiled CCIR trace of a well-formed program, run from the initial state with
the array zero-filled at `base`, produces the program's Lean-level denotation
in the output register.  It is stated in the **defined-denotation** direction,

```
  p.denote = some n → (compiled trace).output = some (n : Int)
```

rather than as an equality of `Option`s.  The reason is precise and worth
recording.  `denoteAInstr` fails on an out-of-range index; the compiled trace
fails there too, because the address `8·i + base` is unmapped.  But the
address is computed in `u64` arithmetic, so `i ↦ (8·i + base) mod 2⁶⁴` is
*not* injective over the whole register range: an out-of-range `i = n + 2⁶¹`
aliases the in-range cell `n`, and there the compiled trace succeeds while the
denotation fails.  Restoring the exact biconditional needs one of

* a **`ptr + integer → ptr` CCIR binary form with unnormalized (abstract)
  address arithmetic** — that is what makes the address map injective, and it
  is currently forbidden both by `CCIR.validateInstruction` (binary
  destinations must be integer-typed) and by
  `C.ValidationRule.pointerArithmetic` ("generated pointer arithmetic is
  outside Profile 1"); or
* an explicit out-of-range trap in the emitted code, costing roughly seven
  extra operations per array access.

Both are fragment-extension decisions, so neither is taken here.  The
defined-denotation direction is the one certificates consume anyway: the
denotation is what the kernel evaluates, and the theorem says the artifact
computes it.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert
open LeanCompCert.Proof
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.MemFragment

/-! ## Layout -/

/-- Bytes per array cell: the array is a `uint64_t[]`. -/
abbrev cellBytes : Nat := 8

/-- The `u64` local holding the byte address under construction. -/
def addrDecl (regCount : Nat) : CCIR.LocalDecl :=
  { id := ⟨regCount + 1⟩, type := .u64 }

/-- The `uint64_t *` local holding the materialized cell pointer. -/
def ptrDecl (regCount : Nat) : CCIR.LocalDecl :=
  { id := ⟨regCount + 2⟩, type := .ptr .u64 }

/-- The `u64` function parameter holding the array base address. -/
def baseDecl (regCount : Nat) : CCIR.LocalDecl :=
  { id := ⟨regCount + 3⟩, type := .u64 }

/-- Byte address of cell `n`, in the order the compiled code builds it.
The literal `8` is `cellBytes`, spelled out so that `omega` sees it. -/
def cellAddr (base : Int) (n : Nat) : Int := (n : Int) * 8 + base

theorem cellAddr_inj {base : Int} {m n : Nat} (h : cellAddr base m = cellAddr base n) :
    m = n := by
  unfold cellAddr at h
  omega

/-! ## Compilation -/

/-- Address computation for cell `regs idxReg`: scale, offset, materialize. -/
def addressStraights (regCount idxReg : Nat) : List StraightInstruction :=
  [ .binary (addrDecl regCount) .mul
      (.local ⟨idxReg + 1⟩) (.uintLit .u64 cellBytes)
  , .binary (addrDecl regCount) .add
      (.local (addrDecl regCount).id) (.local (baseDecl regCount).id)
  , .cast (ptrDecl regCount) (.local (addrDecl regCount).id) ]

/-- One array-machine instruction, compiled into the memory-extended proved
fragment.  Scalar instructions go through `Reflect.compileInstr` unchanged. -/
def compileAInstr (regCount index : Nat) : AInstr → List MInstr
  | .scalar i => (compileInstr index i).map MInstr.straight
  | .load dest idxReg =>
      (addressStraights regCount idxReg).map MInstr.straight ++
        [ .load (regLocal dest) (.local (ptrDecl regCount).id) ]
  | .store idxReg srcReg =>
      (addressStraights regCount idxReg).map MInstr.straight ++
        [ .store (.local (ptrDecl regCount).id) (.local ⟨srcReg + 1⟩) ]

def compileAInstrs (regCount index : Nat) (l : List AInstr) : List MInstr :=
  l.flatMap (compileAInstr regCount index)

/-- `Reflect.preamble` plus declarations for the two array scratch locals, so
that every local a compiled array program mentions has a typed destination
even when the program contains no array access. -/
def apreambleStraights (regCount : Nat) : List StraightInstruction :=
  preamble regCount ++
    [ .assign (addrDecl regCount) (.uintLit .u64 0)
    , .cast (ptrDecl regCount) (.local (addrDecl regCount).id) ]

def apreamble (regCount : Nat) : List MInstr :=
  (apreambleStraights regCount).map MInstr.straight

/-- `Proof.foldTrace` for memory-extended traces. -/
def foldTraceM (count : Nat) (body : Nat → List MInstr) : List MInstr :=
  (List.range count).flatMap body

/-- **The compiled trace of an array program.** -/
def AProgram.compile (p : AProgram) : List MInstr :=
  apreamble p.regCount ++
    compileAInstrs p.regCount 0 p.init ++
    foldTraceM p.loopCount (fun index => compileAInstrs p.regCount index p.body) ++
    compileAInstrs p.regCount 0 p.epilogue

/-! ## Well-formedness -/

def AInstr.WF (regCount : Nat) : AInstr → Prop
  | .scalar i => i.WF regCount
  | .load dest idxReg => dest < regCount ∧ idxReg < regCount
  | .store idxReg srcReg => idxReg < regCount ∧ srcReg < regCount

instance (regCount : Nat) (a : AInstr) : Decidable (a.WF regCount) := by
  cases a <;> simp only [AInstr.WF] <;> infer_instance

def AProgram.WF (p : AProgram) : Prop :=
  p.output < p.regCount ∧
    (∀ a ∈ p.init, a.WF p.regCount) ∧
    (∀ a ∈ p.body, a.WF p.regCount) ∧
    (∀ a ∈ p.epilogue, a.WF p.regCount)

instance (p : AProgram) : Decidable p.WF := by
  unfold AProgram.WF; infer_instance

/-! ## Initial state -/

/-- The array's cells, zero-filled, at the byte addresses `cellAddr base n`
for `n < arrayLen`; every other address is unmapped. -/
def initialMem (arrayLen : Nat) (base : Int) : Mem :=
  fun a =>
    if 0 ≤ a - base ∧ a - base < ((8 * arrayLen : Nat) : Int) ∧ (a - base) % 8 = 0
      then some 0 else none

theorem initialMem_cell (arrayLen : Nat) (base : Int) {n : Nat} (h : n < arrayLen) :
    initialMem arrayLen base (cellAddr base n) = some 0 := by
  unfold initialMem cellAddr
  rw [if_pos]
  refine ⟨by omega, by omega, by omega⟩

/-- The initial memory-extended CCIR state: nothing defined but the base
parameter, and the array zero-filled. -/
def AProgram.initialMCC (p : AProgram) (base : Int) : MCCState :=
  { env := Verified.emptyCCEnv.set (baseDecl p.regCount).id base
    mem := initialMem p.arrayLen base }

/-- The array fits in the `u64` address space without wrapping. -/
def BaseOk (arrayLen : Nat) (base : Int) : Prop :=
  0 ≤ base ∧ base + ((8 * arrayLen : Nat) : Int) ≤ ((M : Nat) : Int)

/-! ## The simulation relation -/

/-- Registers are held by `Reflect`'s `StateInv`; the base parameter is
intact; every in-range cell holds its array value, which is a `u64`. -/
structure ARel (regCount arrayLen : Nat) (base : Int)
    (s : AState) (m : MCCState) : Prop where
  hregs : StateInv regCount s.regs m.env
  hbase : m.env (baseDecl regCount).id = some base
  hcells : ∀ n, n < arrayLen → m.mem (cellAddr base n) = some ((s.arr n : Nat) : Int)
  hcellsLt : ∀ n, n < arrayLen → s.arr n < M

/-- Lock-step in the defined-denotation direction: a successful denotation
step forces a successful, related model step. -/
def AStepRel (regCount arrayLen : Nat) (base : Int) :
    Option AState → Option MCCState → Prop
  | some s, some m => ARel regCount arrayLen base s m
  | some _, none => False
  | none, _ => True

/-! ## Plumbing

Two families of bind lemmas are needed: `MemFragment` writes `Option.bind`
explicitly, while `Proof` and `ArrayState` use `do`-notation, i.e. `>>=`.
-/

private theorem obind_none {α β : Type} (f : α → Option β) :
    Option.bind (none : Option α) f = none := rfl

private theorem obind_some {α β : Type} (a : α) (f : α → Option β) :
    Option.bind (some a) f = f a := rfl

private theorem mbind_none {α β : Type} (f : α → Option β) :
    ((none : Option α) >>= f) = none := rfl

private theorem mbind_some {α β : Type} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

private theorem mbind_some_inv {α β : Type} {o : Option α} {g : α → Option β}
    {b : β} (h : (o >>= g) = some b) : ∃ a, o = some a ∧ g a = some b := by
  cases o with
  | none => rw [mbind_none] at h; exact absurd h (by simp)
  | some a => exact ⟨a, rfl, by rwa [mbind_some] at h⟩

theorem evalMCCSequence_append (m : MCCState) (xs ys : List MInstr) :
    evalMCCSequence m (xs ++ ys) =
      Option.bind (evalMCCSequence m xs) (fun m => evalMCCSequence m ys) := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
      show Option.bind (evalMCC m x) (fun n => evalMCCSequence n (xs ++ ys)) =
        Option.bind (Option.bind (evalMCC m x) (fun n => evalMCCSequence n xs))
          (fun m => evalMCCSequence m ys)
      cases hHead : evalMCC m x with
      | none => rfl
      | some m1 => simpa only [obind_some] using ih m1

theorem evalMCC_straight (m : MCCState) (si : StraightInstruction) :
    evalMCC m (.straight si) =
      (evalCCStraight m.env si).map (fun env => { m with env := env }) := by
  simp only [evalMCC]
  cases evalCCStraight m.env si <;> rfl

/-- A block of scalar instructions runs in the memory-extended model exactly
as it does in the scalar model, with memory carried through. -/
theorem evalMCCSequence_straight (l : List StraightInstruction) (m : MCCState) :
    evalMCCSequence m (l.map MInstr.straight) =
      (evalCCSequence m.env l).map (fun env => { m with env := env }) := by
  induction l generalizing m with
  | nil => rfl
  | cons si rest ih =>
      show Option.bind (evalMCC m (.straight si))
        (fun n => evalMCCSequence n (rest.map MInstr.straight)) =
          ((evalCCStraight m.env si) >>= (fun env => evalCCSequence env rest)).map _
      rw [evalMCC_straight]
      cases hHead : evalCCStraight m.env si with
      | none => rfl
      | some env1 =>
          show evalMCCSequence { m with env := env1 } (rest.map MInstr.straight) = _
          rw [ih { m with env := env1 }]
          rfl

theorem evalMCCSequence_flatMap (body : Nat → List MInstr) :
    ∀ (l : List Nat) (m : MCCState),
      evalMCCSequence m (l.flatMap body) =
        l.foldlM (fun m index => evalMCCSequence m (body index)) m := by
  intro l
  induction l with
  | nil => intro m; rfl
  | cons x xs ih =>
      intro m
      show evalMCCSequence m (body x ++ xs.flatMap body) =
        (x :: xs).foldlM (fun m index => evalMCCSequence m (body index)) m
      rw [evalMCCSequence_append, List.foldlM_cons]
      cases hHead : evalMCCSequence m (body x) with
      | none => rfl
      | some m1 =>
          rw [obind_some]
          exact ih m1

/-! ### Single straight steps -/

theorem evalCCStraight_assign_of {env : CCEnv} {dest : CCIR.LocalDecl}
    {value : CCIR.Operand} {a : Int} (hv : evalOperand env value = some a) :
    evalCCStraight env (.assign dest value) = some (env.set dest.id a) := by
  show ((evalOperand env value) >>= fun r => pure (env.set dest.id r)) = _
  rw [hv]
  rfl

theorem evalCCStraight_cast_of {env : CCEnv} {dest : CCIR.LocalDecl}
    {value : CCIR.Operand} {a b : Int} (hv : evalOperand env value = some a)
    (hn : normalizeCC dest.type a = some b) :
    evalCCStraight env (.cast dest value) = some (env.set dest.id b) := by
  show ((evalOperand env value) >>= fun r =>
    (normalizeCC dest.type r) >>= fun x => pure (env.set dest.id x)) = _
  rw [hv, mbind_some, hn]
  rfl

theorem evalCCStraight_binary_of {env : CCEnv} {dest : CCIR.LocalDecl}
    {op : UnsignedBinary} {lhs rhs : CCIR.Operand} {a b c : Int}
    (hl : evalOperand env lhs = some a) (hr : evalOperand env rhs = some b)
    (hv : evalCCBinary dest.type op a b = some c) :
    evalCCStraight env (.binary dest op lhs rhs) = some (env.set dest.id c) := by
  show ((evalOperand env lhs) >>= fun l => (evalOperand env rhs) >>= fun r =>
    (evalCCBinary dest.type op l r) >>= fun v => pure (env.set dest.id v)) = _
  rw [hl, mbind_some, hr, mbind_some, hv]
  rfl

/-! ### Frame lemmas -/

/-- The single local a straight instruction writes. -/
def destOf : StraightInstruction → CCIR.LocalId
  | .assign dest _ | .binary dest _ _ _
  | .compare dest _ _ _ | .cast dest _ => dest.id

/-- Every straight instruction that succeeds writes exactly its destination. -/
theorem evalCCStraight_shape {env env' : CCEnv} {si : StraightInstruction}
    (h : evalCCStraight env si = some env') :
    ∃ v, env' = env.set (destOf si) v := by
  cases si with
  | assign dest value =>
      simp only [evalCCStraight, evalCCAssignStep] at h
      obtain ⟨a, _, h2⟩ := mbind_some_inv h
      exact ⟨a, (Option.some.inj h2).symm⟩
  | binary dest op lhs rhs =>
      simp only [evalCCStraight, evalCCBinaryStep] at h
      obtain ⟨a, _, h2⟩ := mbind_some_inv h
      obtain ⟨b, _, h3⟩ := mbind_some_inv h2
      obtain ⟨c, _, h4⟩ := mbind_some_inv h3
      exact ⟨c, (Option.some.inj h4).symm⟩
  | compare dest op lhs rhs =>
      simp only [evalCCStraight, evalCCComparisonStep] at h
      obtain ⟨a, _, h2⟩ := mbind_some_inv h
      obtain ⟨b, _, h3⟩ := mbind_some_inv h2
      obtain ⟨c, _, h4⟩ := mbind_some_inv h3
      exact ⟨c, (Option.some.inj h4).symm⟩
  | cast dest value =>
      simp only [evalCCStraight, evalCCCastStep] at h
      obtain ⟨a, _, h2⟩ := mbind_some_inv h
      obtain ⟨b, _, h3⟩ := mbind_some_inv h2
      exact ⟨b, (Option.some.inj h3).symm⟩

theorem evalCCStraight_frame {env env' : CCEnv} {si : StraightInstruction}
    (h : evalCCStraight env si = some env') {j : CCIR.LocalId}
    (hj : j ≠ destOf si) : env' j = env j := by
  obtain ⟨v, rfl⟩ := evalCCStraight_shape h
  simp only [CCEnv.set, if_neg hj]

theorem evalCCSequence_frame :
    ∀ (l : List StraightInstruction) {env env' : CCEnv},
      evalCCSequence env l = some env' →
      ∀ {j : CCIR.LocalId}, (∀ si ∈ l, j ≠ destOf si) → env' j = env j := by
  intro l
  induction l with
  | nil =>
      intro env env' h j _
      cases h
      rfl
  | cons si rest ih =>
      intro env env' h j hj
      simp only [evalCCSequence] at h
      obtain ⟨env1, hs, h2⟩ := mbind_some_inv h
      rw [ih h2 (fun x hx => hj x (List.mem_cons_of_mem _ hx)),
        evalCCStraight_frame hs (hj si (by simp))]

theorem compileInstr_destOf_le {regCount index : Nat} {i : Instr}
    (hWF : i.WF regCount) :
    ∀ si ∈ compileInstr index i, (destOf si).value ≤ regCount := by
  cases i with
  | mov dest src =>
      obtain ⟨hDest, _⟩ := hWF
      intro si hMem
      simp only [compileInstr, List.mem_singleton] at hMem
      subst hMem
      exact hDest
  | binop dest op lhs rhs =>
      obtain ⟨hDest, _, _⟩ := hWF
      intro si hMem
      cases hArith : op.arithmetic? with
      | some arith =>
          rw [show compileInstr index (.binop dest op lhs rhs) =
            [.binary (regLocal dest) arith
              (compileOperand index lhs) (compileOperand index rhs)] from by
              show (match op.arithmetic?, op.comparison? with
                | some arith, _ =>
                    [StraightInstruction.binary (regLocal dest) arith
                      (compileOperand index lhs) (compileOperand index rhs)]
                | none, some comparison =>
                    [StraightInstruction.compare scratchLocal comparison
                      (compileOperand index lhs) (compileOperand index rhs),
                     StraightInstruction.cast (regLocal dest) (.local ⟨0⟩)]
                | none, none => []) = _
              rw [hArith]] at hMem
          simp only [List.mem_singleton] at hMem
          subst hMem
          exact hDest
      | none =>
          cases hCmp : op.comparison? with
          | none =>
              exfalso
              cases op <;> simp [Op.arithmetic?] at hArith <;>
                simp [Op.comparison?] at hCmp
          | some cmp =>
              rw [show compileInstr index (.binop dest op lhs rhs) =
                [.compare scratchLocal cmp
                  (compileOperand index lhs) (compileOperand index rhs),
                 .cast (regLocal dest) (.local ⟨0⟩)] from by
                  show (match op.arithmetic?, op.comparison? with
                    | some arith, _ =>
                        [StraightInstruction.binary (regLocal dest) arith
                          (compileOperand index lhs) (compileOperand index rhs)]
                    | none, some comparison =>
                        [StraightInstruction.compare scratchLocal comparison
                          (compileOperand index lhs) (compileOperand index rhs),
                         StraightInstruction.cast (regLocal dest) (.local ⟨0⟩)]
                    | none, none => []) = _
                  rw [hArith, hCmp]] at hMem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
              cases hMem with
              | inl h => subst h; exact Nat.zero_le _
              | inr h => subst h; exact hDest

theorem compileInstrs_destOf_le {regCount index : Nat} {l : List Instr}
    (hWF : ∀ i ∈ l, i.WF regCount) :
    ∀ si ∈ compileInstrs index l, (destOf si).value ≤ regCount := by
  intro si hMem
  simp only [compileInstrs, List.mem_flatMap] at hMem
  obtain ⟨i, hi, hSi⟩ := hMem
  exact compileInstr_destOf_le (hWF i hi) si hSi

theorem preamble_destOf_le (regCount : Nat) :
    ∀ si ∈ preamble regCount, (destOf si).value ≤ regCount := by
  intro si hMem
  unfold preamble at hMem
  rcases List.mem_cons.mp hMem with hScratch | hTail
  · subst hScratch; exact Nat.zero_le _
  · simp only [List.mem_map, List.mem_range] at hTail
    obtain ⟨i, hi, hSi⟩ := hTail
    subst hSi
    exact hi

/-- Writing a local above the register file preserves `StateInv`. -/
theorem stateInv_set_high {regCount : Nat} {s : RegState} {env : CCEnv}
    (h : StateInv regCount s env) {id : CCIR.LocalId}
    (hid : regCount < id.value) (v : Int) :
    StateInv regCount s (env.set id v) := by
  refine ⟨fun i hi => ?_, h.2⟩
  have hne : (⟨i + 1⟩ : CCIR.LocalId) ≠ id := by
    intro hEq
    have : i + 1 = id.value := congrArg CCIR.LocalId.value hEq
    omega
  simp only [CCEnv.set, if_neg hne]
  exact h.1 i hi

/-- Writing a register preserves `StateInv` (the public counterpart of
`Reflect`'s private `stateInv_set`). -/
theorem stateInv_set_reg {regCount : Nat} {s : RegState} {env : CCEnv}
    (hInv : StateInv regCount s env) (dest value : Nat) (hValue : value < M) :
    StateInv regCount (s.set dest value)
      (env.set ⟨dest + 1⟩ ((value : Nat) : Int)) := by
  constructor
  · intro i hi
    by_cases hEq : i = dest
    · subst hEq
      simp [CCEnv.set, RegState.set]
    · have hId : (⟨i + 1⟩ : CCIR.LocalId) ≠ ⟨dest + 1⟩ := by
        intro h
        injection h with h1
        omega
      simp only [CCEnv.set, RegState.set, if_neg hId, if_neg hEq]
      exact hInv.1 i hi
  · intro i hi
    by_cases hEq : i = dest
    · subst hEq
      simpa [RegState.set] using hValue
    · simp only [RegState.set, if_neg hEq]
      exact hInv.2 i hi

/-! ## The address block -/

private theorem two_pow_64 : ((M : Nat) : Int) = Int.ofNat (2 ^ 64) := rfl

private theorem normalizeCC_ptr_u64_def (x : Int) :
    normalizeCC (.ptr .u64) x = some (x.emod (Int.ofNat (2 ^ 64))) := by
  show (if (Int.ofNat (2 ^ 64)) = 0 then none
    else some (x.emod (Int.ofNat (2 ^ 64)))) = _
  rw [if_neg (by decide)]

private theorem norm_u64_id {x : Int} (h0 : 0 ≤ x) (h1 : x < ((M : Nat) : Int)) :
    normalizeCC .u64 x = some x := by
  rw [normalizeCC_u64_def]
  exact congrArg some (Int.emod_eq_of_lt h0 h1)

private theorem norm_ptr_id {x : Int} (h0 : 0 ≤ x) (h1 : x < ((M : Nat) : Int)) :
    normalizeCC (.ptr .u64) x = some x := by
  rw [normalizeCC_ptr_u64_def]
  exact congrArg some (Int.emod_eq_of_lt h0 h1)

private theorem lit_eight (env : CCEnv) :
    evalOperand env (.uintLit .u64 cellBytes) = some 8 :=
  norm_u64_id (by decide) (by decide)

private theorem lit_zero (env : CCEnv) :
    evalOperand env (.uintLit .u64 0) = some 0 :=
  norm_u64_id (by decide) (by decide)

private theorem addr_ne_base (regCount : Nat) :
    (baseDecl regCount).id ≠ (addrDecl regCount).id := by
  intro hEq
  have := congrArg CCIR.LocalId.value hEq
  simp only [baseDecl, addrDecl] at this
  omega

private theorem ptr_ne_base (regCount : Nat) :
    (baseDecl regCount).id ≠ (ptrDecl regCount).id := by
  intro hEq
  have := congrArg CCIR.LocalId.value hEq
  simp only [baseDecl, ptrDecl] at this
  omega

private theorem addr_high (regCount : Nat) :
    regCount < (addrDecl regCount).id.value := by
  show regCount < regCount + 1
  omega

private theorem ptr_high (regCount : Nat) :
    regCount < (ptrDecl regCount).id.value := by
  show regCount < regCount + 2
  omega

/--
Running the three address instructions from a related state with an in-range
index leaves the registers and the base parameter alone, and puts the exact
byte address `cellAddr base (regs idxReg)` in the cell-pointer local.
-/
theorem addressStraights_correct
    {regCount arrayLen idxReg : Nat} {base : Int}
    (hBase : BaseOk arrayLen base)
    {s : RegState} {env : CCEnv}
    (hInv : StateInv regCount s env)
    (hbase : env (baseDecl regCount).id = some base)
    (hIdx : idxReg < regCount)
    (hLt : s idxReg < arrayLen) :
    ∃ env', evalCCSequence env (addressStraights regCount idxReg) = some env' ∧
      StateInv regCount s env' ∧
      env' (baseDecl regCount).id = some base ∧
      env' (ptrDecl regCount).id = some (cellAddr base (s idxReg)) := by
  obtain ⟨hBase0, hBaseFit⟩ := hBase
  have hIdxVal : env ⟨idxReg + 1⟩ = some ((s idxReg : Nat) : Int) := hInv.1 idxReg hIdx
  have hLtI : ((s idxReg : Nat) : Int) < (arrayLen : Int) := by omega
  have hOff0 : (0 : Int) ≤ ((s idxReg : Nat) : Int) * 8 := by omega
  have hOff1 : ((s idxReg : Nat) : Int) * 8 < ((M : Nat) : Int) := by omega
  have hAddr0 : (0 : Int) ≤ cellAddr base (s idxReg) := by
    show (0 : Int) ≤ ((s idxReg : Nat) : Int) * 8 + base
    omega
  have hAddr1 : cellAddr base (s idxReg) < ((M : Nat) : Int) := by
    show ((s idxReg : Nat) : Int) * 8 + base < ((M : Nat) : Int)
    omega
  obtain ⟨env1, hStep1, hInv1, hbase1, haddr1⟩ :
      ∃ e, evalCCStraight env
          (.binary (addrDecl regCount) .mul
            (.local ⟨idxReg + 1⟩) (.uintLit .u64 cellBytes)) = some e ∧
        StateInv regCount s e ∧
        e (baseDecl regCount).id = some base ∧
        e (addrDecl regCount).id = some (((s idxReg : Nat) : Int) * 8) := by
    refine ⟨env.set (addrDecl regCount).id (((s idxReg : Nat) : Int) * 8),
      evalCCStraight_binary_of hIdxVal (lit_eight env) (norm_u64_id hOff0 hOff1),
      stateInv_set_high hInv (addr_high regCount) _, ?_, ?_⟩
    · simp only [CCEnv.set, if_neg (addr_ne_base regCount)]
      exact hbase
    · simp [CCEnv.set]
  obtain ⟨env2, hStep2, hInv2, hbase2, haddr2⟩ :
      ∃ e, evalCCStraight env1
          (.binary (addrDecl regCount) .add
            (.local (addrDecl regCount).id) (.local (baseDecl regCount).id)) = some e ∧
        StateInv regCount s e ∧
        e (baseDecl regCount).id = some base ∧
        e (addrDecl regCount).id = some (cellAddr base (s idxReg)) := by
    refine ⟨env1.set (addrDecl regCount).id (cellAddr base (s idxReg)),
      evalCCStraight_binary_of haddr1 hbase1 (norm_u64_id hAddr0 hAddr1),
      stateInv_set_high hInv1 (addr_high regCount) _, ?_, ?_⟩
    · simp only [CCEnv.set, if_neg (addr_ne_base regCount)]
      exact hbase1
    · simp [CCEnv.set]
  obtain ⟨env3, hStep3, hInv3, hbase3, hptr3⟩ :
      ∃ e, evalCCStraight env2
          (.cast (ptrDecl regCount) (.local (addrDecl regCount).id)) = some e ∧
        StateInv regCount s e ∧
        e (baseDecl regCount).id = some base ∧
        e (ptrDecl regCount).id = some (cellAddr base (s idxReg)) := by
    refine ⟨env2.set (ptrDecl regCount).id (cellAddr base (s idxReg)),
      evalCCStraight_cast_of haddr2 (norm_ptr_id hAddr0 hAddr1),
      stateInv_set_high hInv2 (ptr_high regCount) _, ?_, ?_⟩
    · simp only [CCEnv.set, if_neg (ptr_ne_base regCount)]
      exact hbase2
    · simp [CCEnv.set]
  refine ⟨env3, ?_, hInv3, hbase3, hptr3⟩
  show ((evalCCStraight env _) >>= fun e => evalCCSequence e _) = _
  rw [hStep1, mbind_some]
  show ((evalCCStraight env1 _) >>= fun e => evalCCSequence e _) = _
  rw [hStep2, mbind_some]
  show ((evalCCStraight env2 _) >>= fun e => evalCCSequence e _) = _
  rw [hStep3, mbind_some]
  rfl

/-- The base parameter survives a compiled scalar instruction. -/
theorem compileInstr_base_frame {regCount index : Nat} {i : Instr}
    (hWF : i.WF regCount) {env env' : CCEnv}
    (h : evalCCSequence env (compileInstr index i) = some env') :
    env' (baseDecl regCount).id = env (baseDecl regCount).id := by
  refine evalCCSequence_frame (compileInstr index i) h (fun si hsi hEq => ?_)
  have hle := compileInstr_destOf_le hWF si hsi
  have hv : (baseDecl regCount).id.value = (destOf si).value :=
    congrArg CCIR.LocalId.value hEq
  simp only [baseDecl] at hv
  omega

/-- The base parameter survives the register preamble. -/
theorem preamble_base_frame {regCount : Nat} {env env' : CCEnv}
    (h : evalCCSequence env (preamble regCount) = some env') :
    env' (baseDecl regCount).id = env (baseDecl regCount).id := by
  refine evalCCSequence_frame (preamble regCount) h (fun si hsi hEq => ?_)
  have hle := preamble_destOf_le regCount si hsi
  have hv : (baseDecl regCount).id.value = (destOf si).value :=
    congrArg CCIR.LocalId.value hEq
  simp only [baseDecl] at hv
  omega

/-! ## One instruction -/

theorem compileAInstr_correct
    {regCount arrayLen index : Nat} {base : Int}
    (hBase : BaseOk arrayLen base)
    {a : AInstr} (hWF : a.WF regCount)
    {s : AState} {m : MCCState} (hRel : ARel regCount arrayLen base s m) :
    AStepRel regCount arrayLen base
      (denoteAInstr arrayLen index s a)
      (evalMCCSequence m (compileAInstr regCount index a)) := by
  cases a with
  | scalar i =>
      simp only [AInstr.WF] at hWF
      rw [denoteAInstr_scalar]
      show AStepRel regCount arrayLen base _
        (evalMCCSequence m ((compileInstr index i).map MInstr.straight))
      rw [evalMCCSequence_straight]
      have hStep := denoteInstr_correct index regCount s.regs m.env hRel.hregs i hWF
      cases hD : denoteInstr index s.regs i with
      | none => trivial
      | some regs =>
          rw [hD] at hStep
          cases hE : evalCCSequence m.env (compileInstr index i) with
          | none => rw [hE] at hStep; exact absurd hStep (by simp [StepRel])
          | some env1 =>
              rw [hE] at hStep
              refine ⟨hStep, ?_, hRel.hcells, hRel.hcellsLt⟩
              show env1 (baseDecl regCount).id = some base
              rw [compileInstr_base_frame hWF hE]
              exact hRel.hbase
  | load dest idxReg =>
      obtain ⟨hDest, hIdx⟩ := hWF
      simp only [denoteAInstr]
      split
      · rename_i hLt
        obtain ⟨env', hRun, hInv', hbase', hptr'⟩ :=
          addressStraights_correct hBase hRel.hregs hRel.hbase hIdx hLt
        show AStepRel regCount arrayLen base _
          (evalMCCSequence m
            ((addressStraights regCount idxReg).map MInstr.straight ++ _))
        rw [evalMCCSequence_append, evalMCCSequence_straight, hRun]
        show AStepRel regCount arrayLen base _
          (evalMCCSequence { m with env := env' }
            [MInstr.load (regLocal dest) (.local (ptrDecl regCount).id)])
        have hCell := hRel.hcells (s.regs idxReg) hLt
        have hLoad : evalMCCSequence { m with env := env' }
            [MInstr.load (regLocal dest) (.local (ptrDecl regCount).id)] =
            some { env := env'.set (regLocal dest).id
                     ((s.arr (s.regs idxReg) : Nat) : Int)
                 , mem := m.mem } := by
          show Option.bind (evalMCC { m with env := env' }
            (.load (regLocal dest) (.local (ptrDecl regCount).id))) _ = _
          show Option.bind (Option.bind
            (evalOperand env' (.local (ptrDecl regCount).id)) _) _ = _
          rw [show evalOperand env' (.local (ptrDecl regCount).id) =
            some (cellAddr base (s.regs idxReg)) from hptr']
          show Option.bind (Option.bind (m.mem (cellAddr base (s.regs idxReg))) _) _ = _
          rw [hCell]
          rfl
        rw [hLoad]
        refine ⟨?_, ?_, ?_, hRel.hcellsLt⟩
        · exact stateInv_set_reg hInv' dest _ (hRel.hcellsLt _ hLt)
        · have hne : (baseDecl regCount).id ≠ (regLocal dest).id := by
            intro hEq
            have := congrArg CCIR.LocalId.value hEq
            simp only [baseDecl, regLocal] at this
            omega
          show (env'.set (regLocal dest).id _) (baseDecl regCount).id = _
          simp only [CCEnv.set, if_neg hne]
          exact hbase'
        · exact hRel.hcells
      · trivial
  | store idxReg srcReg =>
      obtain ⟨hIdx, hSrc⟩ := hWF
      simp only [denoteAInstr]
      split
      · rename_i hLt
        obtain ⟨env', hRun, hInv', hbase', hptr'⟩ :=
          addressStraights_correct hBase hRel.hregs hRel.hbase hIdx hLt
        show AStepRel regCount arrayLen base _
          (evalMCCSequence m
            ((addressStraights regCount idxReg).map MInstr.straight ++ _))
        rw [evalMCCSequence_append, evalMCCSequence_straight, hRun]
        show AStepRel regCount arrayLen base _
          (evalMCCSequence { m with env := env' }
            [MInstr.store (.local (ptrDecl regCount).id) (.local ⟨srcReg + 1⟩)])
        have hSrcVal : env' ⟨srcReg + 1⟩ = some ((s.regs srcReg : Nat) : Int) :=
          hInv'.1 srcReg hSrc
        have hStore : evalMCCSequence { m with env := env' }
            [MInstr.store (.local (ptrDecl regCount).id) (.local ⟨srcReg + 1⟩)] =
            some { env := env'
                 , mem := Mem.set m.mem (cellAddr base (s.regs idxReg))
                     ((s.regs srcReg : Nat) : Int) } := by
          show Option.bind (evalMCC { m with env := env' }
            (.store (.local (ptrDecl regCount).id) (.local ⟨srcReg + 1⟩))) _ = _
          show Option.bind (Option.bind
            (evalOperand env' (.local (ptrDecl regCount).id)) _) _ = _
          rw [show evalOperand env' (.local (ptrDecl regCount).id) =
            some (cellAddr base (s.regs idxReg)) from hptr']
          show Option.bind (Option.bind
            (evalOperand env' (.local ⟨srcReg + 1⟩)) _) _ = _
          rw [show evalOperand env' (.local ⟨srcReg + 1⟩) =
            some ((s.regs srcReg : Nat) : Int) from hSrcVal]
          rfl
        rw [hStore]
        refine ⟨hInv', hbase', ?_, ?_⟩
        · intro n hn
          show Mem.set m.mem (cellAddr base (s.regs idxReg))
            ((s.regs srcReg : Nat) : Int) (cellAddr base n) = _
          simp only [Mem.set]
          by_cases hEq : n = s.regs idxReg
          · subst hEq
            rw [if_pos rfl]
            simp [AState.writeArr]
          · rw [if_neg (fun hc => hEq (cellAddr_inj hc))]
            rw [hRel.hcells n hn]
            simp [AState.writeArr, hEq]
        · intro n hn
          show (if n = s.regs idxReg then s.regs srcReg else s.arr n) < M
          by_cases hEq : n = s.regs idxReg
          · rw [if_pos hEq]; exact hRel.hregs.2 srcReg hSrc
          · rw [if_neg hEq]; exact hRel.hcellsLt n hn
      · trivial

/-! ## Blocks, folds, and the bridge -/

theorem compileAInstrs_correct
    {regCount arrayLen index : Nat} {base : Int}
    (hBase : BaseOk arrayLen base) (l : List AInstr)
    (hWF : ∀ a ∈ l, a.WF regCount) :
    ∀ (s : AState) (m : MCCState), ARel regCount arrayLen base s m →
      AStepRel regCount arrayLen base
        (denoteAInstrs arrayLen index s l)
        (evalMCCSequence m (compileAInstrs regCount index l)) := by
  induction l with
  | nil => intro s m hRel; exact hRel
  | cons a rest ih =>
      intro s m hRel
      have hStep := compileAInstr_correct (index := index) hBase (hWF a (by simp)) hRel
      show AStepRel regCount arrayLen base
        (Option.bind (denoteAInstr arrayLen index s a)
          (fun s => denoteAInstrs arrayLen index s rest))
        (evalMCCSequence m (compileAInstr regCount index a ++
          compileAInstrs regCount index rest))
      rw [evalMCCSequence_append]
      cases hD : denoteAInstr arrayLen index s a with
      | none => trivial
      | some s1 =>
          rw [hD] at hStep
          cases hE : evalMCCSequence m (compileAInstr regCount index a) with
          | none => rw [hE] at hStep; exact hStep.elim
          | some m1 =>
              rw [hE] at hStep
              exact ih (fun x hx => hWF x (by simp [hx])) s1 m1 hStep

theorem foldBodyA_correct
    {regCount arrayLen : Nat} {base : Int}
    (hBase : BaseOk arrayLen base) (body : List AInstr)
    (hWF : ∀ a ∈ body, a.WF regCount) (indices : List Nat) :
    ∀ (s : AState) (m : MCCState), ARel regCount arrayLen base s m →
      AStepRel regCount arrayLen base
        (indices.foldlM (fun s index => denoteAInstrs arrayLen index s body) s)
        (indices.foldlM
          (fun m index => evalMCCSequence m (compileAInstrs regCount index body)) m) := by
  induction indices with
  | nil => intro s m hRel; exact hRel
  | cons index rest ih =>
      intro s m hRel
      have hStep := compileAInstrs_correct (index := index) hBase body hWF s m hRel
      rw [List.foldlM_cons, List.foldlM_cons]
      cases hD : denoteAInstrs arrayLen index s body with
      | none => trivial
      | some s1 =>
          rw [hD] at hStep
          cases hE : evalMCCSequence m (compileAInstrs regCount index body) with
          | none => rw [hE] at hStep; exact hStep.elim
          | some m1 =>
              rw [hE] at hStep
              exact ih s1 m1 hStep

/-- The preamble installs the zeroed register file, leaves the base parameter
alone and never touches memory. -/
theorem apreamble_correct (p : AProgram) (base : Int) :
    ∃ env0, evalCCSequence (p.initialMCC base).env
        (apreambleStraights p.regCount) = some env0 ∧
      StateInv p.regCount initialState env0 ∧
      env0 (baseDecl p.regCount).id = some base := by
  obtain ⟨envMid, hMid, hRegs⟩ :=
    preamble_correct p.regCount (p.initialMCC base).env
  have hbaseMid : envMid (baseDecl p.regCount).id = some base := by
    rw [preamble_base_frame hMid]
    show (Verified.emptyCCEnv.set (baseDecl p.regCount).id base)
      (baseDecl p.regCount).id = some base
    simp [CCEnv.set]
  have hInvMid : StateInv p.regCount initialState envMid :=
    ⟨fun i hi => hRegs i hi, fun i _ => M_pos⟩
  obtain ⟨env1, hStep1, hInv1, hbase1, haddr1⟩ :
      ∃ e, evalCCStraight envMid
          (.assign (addrDecl p.regCount) (.uintLit .u64 0)) = some e ∧
        StateInv p.regCount initialState e ∧
        e (baseDecl p.regCount).id = some base ∧
        e (addrDecl p.regCount).id = some 0 := by
    refine ⟨envMid.set (addrDecl p.regCount).id 0,
      evalCCStraight_assign_of (lit_zero envMid),
      stateInv_set_high hInvMid (addr_high p.regCount) _, ?_, ?_⟩
    · simp only [CCEnv.set, if_neg (addr_ne_base p.regCount)]
      exact hbaseMid
    · simp [CCEnv.set]
  obtain ⟨env2, hStep2, hInv2, hbase2⟩ :
      ∃ e, evalCCStraight env1
          (.cast (ptrDecl p.regCount) (.local (addrDecl p.regCount).id)) = some e ∧
        StateInv p.regCount initialState e ∧
        e (baseDecl p.regCount).id = some base := by
    refine ⟨env1.set (ptrDecl p.regCount).id 0,
      evalCCStraight_cast_of haddr1 (norm_ptr_id (by decide) (by decide)),
      stateInv_set_high hInv1 (ptr_high p.regCount) _, ?_⟩
    · simp only [CCEnv.set, if_neg (ptr_ne_base p.regCount)]
      exact hbase1
  refine ⟨env2, ?_, hInv2, hbase2⟩
  unfold apreambleStraights
  rw [evalCCSequence_append, hMid, mbind_some]
  show ((evalCCStraight envMid _) >>= fun e => evalCCSequence e _) = _
  rw [hStep1, mbind_some]
  show ((evalCCStraight env1 _) >>= fun e => evalCCSequence e _) = _
  rw [hStep2, mbind_some]
  rfl

/--
**The array reflection bridge.**  The compiled CCIR trace of a well-formed
array program, run from the zero-filled array at `base`, computes exactly the
program's Lean-level denotation in the output register.

This is `Reflect.Program.evalCC_compile` for `AProgram`; see the module
docstring for why it is stated in the defined-denotation direction.
-/
theorem AProgram.evalCC_compile (p : AProgram) (hWF : p.WF) (base : Int)
    (hBase : BaseOk p.arrayLen base) (n : Nat) (hDenote : p.denote = some n) :
    Option.bind (evalMCCSequence (p.initialMCC base) p.compile)
        (fun m => m.env ⟨p.output + 1⟩) = some ((n : Nat) : Int) := by
  obtain ⟨hOutput, hInit, hBody, hEpilogue⟩ := hWF
  obtain ⟨env0, hPre, hInv0, hbase0⟩ := apreamble_correct p base
  have hRel0 : ARel p.regCount p.arrayLen base initialAState
      { env := env0, mem := (p.initialMCC base).mem } := by
    refine ⟨hInv0, hbase0, ?_, ?_⟩
    · intro k hk
      show initialMem p.arrayLen base (cellAddr base k) = some ((0 : Nat) : Int)
      rw [initialMem_cell p.arrayLen base hk]
      rfl
    · intro k _; exact M_pos
  unfold AProgram.compile
  rw [List.append_assoc, List.append_assoc, evalMCCSequence_append]
  rw [show evalMCCSequence (p.initialMCC base) (apreamble p.regCount) =
      some { env := env0, mem := (p.initialMCC base).mem } from by
    unfold apreamble
    rw [evalMCCSequence_straight, hPre]
    rfl]
  simp only [obind_some]
  rw [evalMCCSequence_append]
  unfold AProgram.denote at hDenote
  -- init block
  have hInitStep := compileAInstrs_correct (index := 0) hBase p.init hInit
    initialAState _ hRel0
  cases hInitD : denoteAInstrs p.arrayLen 0 initialAState p.init with
  | none => rw [hInitD] at hDenote; exact absurd hDenote (by simp)
  | some s1 =>
      rw [hInitD] at hInitStep hDenote
      cases hInitE : evalMCCSequence { env := env0, mem := (p.initialMCC base).mem }
          (compileAInstrs p.regCount 0 p.init) with
      | none => rw [hInitE] at hInitStep; exact hInitStep.elim
      | some m1 =>
          rw [hInitE] at hInitStep
          simp only [obind_some, mbind_some] at hDenote ⊢
          rw [evalMCCSequence_append]
          -- loop
          have hFoldStep := foldBodyA_correct hBase p.body hBody
            (List.range p.loopCount) s1 m1 hInitStep
          rw [show evalMCCSequence m1
              (foldTraceM p.loopCount
                (fun index => compileAInstrs p.regCount index p.body)) =
              (List.range p.loopCount).foldlM
                (fun m index =>
                  evalMCCSequence m (compileAInstrs p.regCount index p.body)) m1 from
            evalMCCSequence_flatMap _ _ _]
          cases hFoldD : (List.range p.loopCount).foldlM
              (fun s index => denoteAInstrs p.arrayLen index s p.body) s1 with
          | none => rw [hFoldD] at hDenote; exact absurd hDenote (by simp)
          | some s2 =>
              rw [hFoldD] at hFoldStep hDenote
              cases hFoldE : (List.range p.loopCount).foldlM
                  (fun m index =>
                    evalMCCSequence m (compileAInstrs p.regCount index p.body)) m1 with
              | none => rw [hFoldE] at hFoldStep; exact hFoldStep.elim
              | some m2 =>
                  rw [hFoldE] at hFoldStep
                  simp only [obind_some, mbind_some] at hDenote ⊢
                  -- epilogue
                  have hEpiStep := compileAInstrs_correct (index := 0) hBase
                    p.epilogue hEpilogue s2 m2 hFoldStep
                  cases hEpiD : denoteAInstrs p.arrayLen 0 s2 p.epilogue with
                  | none => rw [hEpiD] at hDenote; exact absurd hDenote (by simp)
                  | some s3 =>
                      rw [hEpiD] at hEpiStep hDenote
                      cases hEpiE : evalMCCSequence m2
                          (compileAInstrs p.regCount 0 p.epilogue) with
                      | none => rw [hEpiE] at hEpiStep; exact hEpiStep.elim
                      | some m3 =>
                          rw [hEpiE] at hEpiStep
                          simp only [obind_some, mbind_some] at hDenote ⊢
                          have : s3.regs p.output = n := by
                            simpa using hDenote
                          rw [← this]
                          exact hEpiStep.hregs.1 p.output hOutput

end LeanCompCert.Verified.ArrayState

import LeanCompCert.Verified.Packed
import LeanCompCert.Verified.ArrayState

/-!
# The packed backend, plugged into the existing verified chain

`LeanCompCert.Verified.Packed` builds a state out of one big `Nat`. This
module makes it a **selectable backend** for the register machine of
`Reflect` and the array of `ArrayState`, by proving that the packed
denotation equals the existing one. Nothing in `Reflect` or
`ArrayState` changes, and no theorem about them is re-proved: the
existing bridge `Reflect.Program.evalCC_compile` — and therefore the
whole CCIR/CompCert chain behind it — applies verbatim to a packed run
through `Program.denotePacked_eq_denote`.

The 64-bit lane width is not a coincidence: `Packed.lane_lt` says every
lane is below `2 ^ 64`, which is exactly the `s i < M` invariant that
`Reflect.StateInv` otherwise has to carry by hand.

## Main results

* `laneState_poke_eq_set` — `poke` denotes `RegState.set`.
* `denoteInstrsPacked_eq` — a packed instruction block denotes the same
  state transformation as the functional one.
* `Program.denotePacked_eq_denote` — **the backend equation**: a whole
  program's packed run agrees with its functional run, so the packed
  backend inherits semantic preservation for free.
* `arrState_poke_eq_writeArr` — the same statement for the array field
  of `ArrayState.AState`.
-/

namespace LeanCompCert.Verified.Packed

open LeanCompCert.Verified.Reflect

/-! ## The register machine -/

/-- `M`, the `u64` modulus of `Reflect`, is the 64-bit lane modulus. -/
theorem laneMod_64 : laneMod 64 = Reflect.M := by
  rw [laneMod_eq]; rfl

/-- Every lane of a 64-bit packed state is a legal `u64` register value —
the `Reflect.StateInv` bound, for free. -/
theorem lane64_lt_M (bits i : Nat) : lane 64 bits i < Reflect.M := by
  have := lane_lt 64 bits i
  rw [show Reflect.M = 2 ^ 64 from rfl]
  exact this

/-- `poke` denotes exactly `RegState.set`. -/
theorem laneState_poke_eq_set (bits i v : Nat) (hv : v < Reflect.M) :
    laneState 64 (poke 64 bits i v) = RegState.set (laneState 64 bits) i v := by
  have hmod : v % laneMod 64 = v := by
    rw [laneMod_64]; exact Nat.mod_eq_of_lt hv
  rw [laneState_poke, hmod]
  rfl

/-! ### Packed denotation of the register fragment -/

/-- Operand denotation against a packed state. -/
def denoteOperandPacked (index bits : Nat) : Operand → Nat
  | .reg i => lane 64 bits i
  | .lit value => value % Reflect.M
  | .idx => index % Reflect.M

theorem denoteOperandPacked_eq (index bits : Nat) (operand : Operand) :
    denoteOperandPacked index bits operand =
      denoteOperand index (laneState 64 bits) operand := by
  cases operand <;> rfl

theorem denoteOperandPacked_lt (index bits : Nat) (operand : Operand) :
    denoteOperandPacked index bits operand < Reflect.M := by
  cases operand with
  | reg i => exact lane64_lt_M bits i
  | lit value => exact Nat.mod_lt _ Reflect.M_pos
  | idx => exact Nat.mod_lt _ Reflect.M_pos

/-- One instruction, executed on the packed state. -/
def denoteInstrPacked (index bits : Nat) : Instr → Option Nat
  | .mov dest src =>
      some (poke 64 bits dest (denoteOperandPacked index bits src))
  | .binop dest op lhs rhs =>
      (denoteOp op (denoteOperandPacked index bits lhs)
        (denoteOperandPacked index bits rhs)).map (poke 64 bits dest)

/-- A block of instructions, executed on the packed state. -/
def denoteInstrsPacked (index bits : Nat) : List Instr → Option Nat
  | [] => some bits
  | instr :: rest => do
      denoteInstrsPacked index (← denoteInstrPacked index bits instr) rest

theorem denoteInstrPacked_eq (index bits : Nat) (instr : Instr) :
    (denoteInstrPacked index bits instr).map (laneState 64) =
      denoteInstr index (laneState 64 bits) instr := by
  cases instr with
  | mov dest src =>
      show some (laneState 64 (poke 64 bits dest _)) = _
      rw [laneState_poke_eq_set bits dest _
        (denoteOperandPacked_lt index bits src),
        denoteOperandPacked_eq]
      rfl
  | binop dest op lhs rhs =>
      show ((denoteOp op _ _).map (poke 64 bits dest)).map (laneState 64) = _
      rw [denoteOperandPacked_eq, denoteOperandPacked_eq]
      cases hResult : denoteOp op (denoteOperand index (laneState 64 bits) lhs)
          (denoteOperand index (laneState 64 bits) rhs) with
      | none =>
          show _ = (denoteOp op _ _).bind _
          rw [hResult]
          rfl
      | some result =>
          show some (laneState 64 (poke 64 bits dest result)) = _
          rw [laneState_poke_eq_set bits dest result
            (denoteOp_lt op _ _ result hResult)]
          show _ = (denoteOp op _ _).bind _
          rw [hResult]
          rfl

/-- **The block equation**: a packed block denotes the same functional
state transformation as the existing one. -/
theorem denoteInstrsPacked_eq (index : Nat) (instrs : List Instr) :
    ∀ bits : Nat,
    (denoteInstrsPacked index bits instrs).map (laneState 64) =
      denoteInstrs index (laneState 64 bits) instrs := by
  induction instrs with
  | nil => intro bits; rfl
  | cons instr rest ih =>
      intro bits
      have hStep := denoteInstrPacked_eq index bits instr
      show ((denoteInstrPacked index bits instr).bind
        (fun b => denoteInstrsPacked index b rest)).map (laneState 64) = _
      cases hInstr : denoteInstrPacked index bits instr with
      | none =>
          rw [hInstr] at hStep
          show (none : Option Nat).map _ = _
          show none = denoteInstr index (laneState 64 bits) instr >>= _
          rw [← hStep]
          rfl
      | some next =>
          rw [hInstr] at hStep
          show (denoteInstrsPacked index next rest).map (laneState 64) = _
          rw [ih next]
          show _ = denoteInstr index (laneState 64 bits) instr >>= _
          rw [← hStep]
          rfl

/-- The packed run of a whole `Reflect.Program`. -/
def _root_.LeanCompCert.Verified.Reflect.Program.denotePacked
    (p : Program) : Option Nat := do
  let bits ← denoteInstrsPacked 0 0 p.init
  let bits ← (List.range p.loopCount).foldlM
    (fun bits index => denoteInstrsPacked index bits p.body) bits
  let bits ← denoteInstrsPacked 0 bits p.epilogue
  pure (lane 64 bits p.output)

private theorem foldPacked_eq (body : List Instr) (indices : List Nat) :
    ∀ bits : Nat,
    (indices.foldlM (fun bits index => denoteInstrsPacked index bits body)
        bits).map (laneState 64) =
      indices.foldlM (fun s index => denoteInstrs index s body)
        (laneState 64 bits) := by
  induction indices with
  | nil => intro bits; rfl
  | cons index rest ih =>
      intro bits
      have hStep := denoteInstrsPacked_eq index body bits
      show ((denoteInstrsPacked index bits body).bind _).map (laneState 64) = _
      cases hBlock : denoteInstrsPacked index bits body with
      | none =>
          rw [hBlock] at hStep
          show (none : Option Nat).map _ = _
          show none = (denoteInstrs index (laneState 64 bits) body) >>= _
          rw [← hStep]
          rfl
      | some next =>
          rw [hBlock] at hStep
          show Option.map (laneState 64)
            (rest.foldlM
              (fun bits index => denoteInstrsPacked index bits body) next) = _
          rw [ih next]
          show _ = (denoteInstrs index (laneState 64 bits) body) >>= _
          rw [← hStep]
          rfl

/-- Transferring a monadic bind across the abstraction function. -/
private theorem bind_congr_lane {γ : Type _}
    {oa : Option Nat} {ob : Option (Nat → Nat)}
    (h : oa.map (laneState 64) = ob)
    (k : Nat → Option γ) (k' : (Nat → Nat) → Option γ)
    (hk : ∀ b, k b = k' (laneState 64 b)) :
    oa >>= k = ob >>= k' := by
  cases oa with
  | none => simp only [Option.map_none] at h; subst h; rfl
  | some a =>
      simp only [Option.map_some] at h
      subst h
      simpa using hk a

/--
**The backend equation.**

A program's packed run and its functional run agree. Everything already
proved about `Program.denote` — in particular the reflection bridge
`Program.evalCC_compile`, and through it the CCIR and generated-C
semantics — therefore holds of the packed backend without being
re-proved. Selecting the backend is rewriting along this equation.
-/
theorem Program.denotePacked_eq_denote (p : Program) :
    p.denotePacked = p.denote := by
  have hInit : (denoteInstrsPacked 0 0 p.init).map (laneState 64)
      = denoteInstrs 0 Reflect.initialState p.init := by
    rw [denoteInstrsPacked_eq, laneState_zero]; rfl
  refine bind_congr_lane hInit _ _ (fun b1 => ?_)
  refine bind_congr_lane (foldPacked_eq p.body (List.range p.loopCount) b1)
    _ _ (fun b2 => ?_)
  refine bind_congr_lane (denoteInstrsPacked_eq 0 p.epilogue b2)
    _ _ (fun b3 => ?_)
  rfl

/-! ## The array backend

The same abstraction function serves `ArrayState`: a packed `Nat` with
`w`-bit lanes denotes the `arr : Nat → Nat` field, and `poke` denotes
`AState.writeArr`. The lane width is a free parameter here — an array of
counters that provably stay below `2 ^ 8` can be packed eight times
denser than a `u64` array.
-/

open LeanCompCert.Verified.ArrayState in
/-- `poke` denotes `AState.writeArr` on the array field. -/
theorem arrState_poke_eq_writeArr
    (w : Nat) (s : AState) (bits i v : Nat)
    (harr : s.arr = laneState w bits) (hv : v < 2 ^ w) :
    (s.writeArr i v).arr = laneState w (poke w bits i v) := by
  have hmod : v % laneMod w = v := by
    rw [laneMod_eq]; exact Nat.mod_eq_of_lt hv
  rw [laneState_poke, hmod]
  funext c
  by_cases h : c = i
  · subst h; simp [AState.writeArr]
  · simp [AState.writeArr, h, harr]

end LeanCompCert.Verified.Packed

import LeanCompCert.Ports.Section413G2Program

/-!
Emitter and cross-check driver for the §4.1.3 `g₂` sweep array program.

Modes:

* `emit CAP ROUNDS CHECKLO OUT` — emit the rolled C artifact for the
  configuration `⟨CAP, ROUNDS, CHECKLO⟩` into `OUT`.  The appended driver
  prints the violation flag and exits `0` iff the flag is `0`.
  Production: `emit 1000000 999 33 g2_prod.c`; smoke: `emit 2000 999 33 …`.

* `check` — the three-way agreement test at kernel-friendly sizes: for
  each tiny configuration, run

  1. the reference model `Section413Sweep.g2Run` (the Boolean the
     downstream proof consumes),
  2. the transparent model `Cfg.tRun` (plain-`Nat` machine semantics), and
  3. the machine itself, `(g2Program c).denote`, through the `AProgram`
     interpreter,

  and print all three with their `g` cells (decoded).  Any disagreement is
  a transcription bug; agreement is evidence (not proof) for the two
  pending simulation obligations.

Emission only; no proof obligation is discharged here.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.Section413G2Program

namespace Bench.Section413SweepEmit

def driver (name : String) (cells : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString cells ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t r = l_" ++ name ++ "(cells);\n" ++
  "    printf(\"flag=%llu\\n\", (unsigned long long)r);\n" ++
  "    return r == 0 ? 0 : 1;\n}\n"

/-- Decode an encoded endpoint for printing. -/
def dec (w : Nat) : Int :=
  if w < 9223372036854775808 then (w : Int)
  else (w : Int) - 18446744073709551616

/-! ### An array-backed evaluator of `AProgram.denote`

`AProgram.denote` threads the register file and the array as closure
chains; the interpreter's recursion depth is the total number of writes,
which this body exceeds within fifty iterations.  This evaluator mirrors
`denoteAInstr` semantics over mutable arrays instead — valid for programs
whose register indices are below `regCount` (proved: `g2Program_wf`).  It
is an **untrusted cross-check tool**, not part of any proof. -/

def evalOp : Verified.Reflect.Op → Nat → Nat → Option Nat
  | .add, a, b => some ((a + b) % Verified.Reflect.M)
  | .sub, a, b => some ((a + (Verified.Reflect.M - b)) % Verified.Reflect.M)
  | .mul, a, b => some ((a * b) % Verified.Reflect.M)
  | .udiv, a, b => if b = 0 then none else some ((a / b) % Verified.Reflect.M)
  | .urem, a, b => if b = 0 then none else some ((a % b) % Verified.Reflect.M)
  | .band, a, b => some ((a &&& b) % Verified.Reflect.M)
  | .bor, a, b => some ((a ||| b) % Verified.Reflect.M)
  | .bxor, a, b => some ((a ^^^ b) % Verified.Reflect.M)
  | .shl, a, b => some ((a <<< b) % Verified.Reflect.M)
  | .lshr, a, b => some ((a >>> b) % Verified.Reflect.M)
  | .eq, a, b => some (if a = b then 1 else 0)
  | .ne, a, b => some (if a ≠ b then 1 else 0)
  | .lt, a, b => some (if a < b then 1 else 0)
  | .le, a, b => some (if a ≤ b then 1 else 0)
  | .gt, a, b => some (if a > b then 1 else 0)
  | .ge, a, b => some (if a ≥ b then 1 else 0)

structure FastState where
  regs : Array Nat
  arr : Array Nat

def fastInstr (len index : Nat) (s : FastState) :
    AInstr → Option FastState
  | .scalar (.mov d src) =>
      let v := match src with
        | .reg i => s.regs[i]!
        | .lit v => v % Verified.Reflect.M
        | .idx => index % Verified.Reflect.M
      some { s with regs := s.regs.set! d v }
  | .scalar (.binop d op l r) => do
      let rd := fun (o : Verified.Reflect.Operand) => match o with
        | .reg i => s.regs[i]!
        | .lit v => v % Verified.Reflect.M
        | .idx => index % Verified.Reflect.M
      let v ← evalOp op (rd l) (rd r)
      some { s with regs := s.regs.set! d v }
  | .load dest idxReg =>
      if s.regs[idxReg]! < len then
        some { s with regs := s.regs.set! dest s.arr[s.regs[idxReg]!]! }
      else none
  | .store idxReg srcReg =>
      if s.regs[idxReg]! < len then
        some { s with arr := s.arr.set! s.regs[idxReg]! s.regs[srcReg]! }
      else none

def fastBlock (len index : Nat) : FastState → List AInstr →
    Option FastState
  | s, [] => some s
  | s, i :: rest => do fastBlock len index (← fastInstr len index s i) rest

/-- Evaluate; also return the final `g` registers for the cross-check. -/
def fastEval (p : AProgram) : Option (Nat × Nat × Nat) := do
  let s0 : FastState :=
    ⟨.replicate p.regCount 0, .replicate p.arrayLen 0⟩
  let s1 ← fastBlock p.arrayLen 0 s0 p.init
  let mut s := s1
  for index in [0:p.loopCount] do
    match fastBlock p.arrayLen index s p.body with
    | none => return ← none
    | some s' => s := s'
  let s2 ← fastBlock p.arrayLen 0 s p.epilogue
  pure (s2.regs[p.output]!, s2.regs[12]!, s2.regs[13]!)

def checkOne (cap rounds checkLo : Nat) (withTransparent : Bool) :
    IO Bool := do
  let c : Cfg := ⟨cap, rounds, checkLo⟩
  -- reference model
  let m := Ports.Section413Sweep.g2Run rounds checkLo cap
  -- the machine, through the array-backed evaluator
  let d := fastEval (g2Program c)
  let mg := s!"[{m.g.lo}, {m.g.hi}]"
  IO.println s!"cfg (cap={cap}, R={rounds}, lo={checkLo}):"
  IO.println s!"  reference   ok={m.ok}  g={mg}"
  let mut agree := true
  match d with
  | none =>
      IO.println "  machine     FAILED (none)"
      agree := false
  | some (flag, gLo, gHi) =>
      IO.println s!"  machine     flag={flag}  g=[{dec gLo}, {dec gHi}]"
      agree := (m.ok == (flag == 0))
        && dec gLo == m.g.lo && dec gHi == m.g.hi
  if withTransparent then
    -- the transparent model (closure array: small configurations only)
    let t := c.tRun
    IO.println s!"  transparent flag={t.viol}  g=[{dec t.gLo}, {dec t.gHi}]"
    agree := agree && (some (t.viol, t.gLo, t.gHi) == d)
  IO.println s!"  agree={agree}"
  pure agree

end Bench.Section413SweepEmit

open Bench.Section413SweepEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["check"] =>
      let mut ok := true
      -- machine ∘ transparent ∘ reference at small sizes (the transparent
      -- model's closure array bounds the recursion depth at about (48, 7))
      for (cap, r, lo) in
          [(6, 2, 2), (12, 3, 34), (30, 5, 33), (48, 7, 33)] do
        ok := (← checkOne cap r lo true) && ok
      -- machine ∘ reference at the full trial-division depth
      for (cap, r, lo) in [(60, 7, 33), (300, 99, 33), (300, 999, 33)] do
        ok := (← checkOne cap r lo false) && ok
      IO.println (if ok then "ALL AGREE" else "DISAGREEMENT")
      return (if ok then 0 else 1)
  | ["emit", capStr, rStr, loStr, out] =>
      let some cap := capStr.toNat? | do IO.eprintln "bad cap"; return 1
      let some r := rStr.toNat? | do IO.eprintln "bad rounds"; return 1
      let some lo := loStr.toNat? | do IO.eprintln "bad checkLo"; return 1
      let c : Cfg := ⟨cap, r, lo⟩
      let p := g2Program c
      let name := s!"S413G2c{cap}"
      match p.emitRolled name with
      | .error errs => (for e in errs do IO.eprintln e); return 1
      | .ok src =>
          IO.FS.writeFile out (src ++ driver name p.arrayLen)
          IO.println s!"emitted cap={cap} rounds={r} checkLo={lo} \
            arrayLen={p.arrayLen} loopCount={p.loopCount} \
            body={p.body.length} instrs"
          return 0
  | _ => do
      IO.eprintln "usage: check | emit CAP ROUNDS CHECKLO OUT"
      return 1

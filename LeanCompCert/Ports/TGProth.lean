import LeanCompCert.Verified.Mont2
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Verified.Rolled

/-!
# Stage (b) of the Helfgott–Platt prime ladder: the Proth test

`bench/results/tg_goldbach.md` recorded stage (b) — `ProthTester::test` —
as **not expressible** in the proved fragment, and it is 75.1 % of the
reference producer's cost.  The binding obstruction named there was the
width of the *division*: `mpz_powm` needs `x·y mod N` for a ~90-bit `N`,
i.e. a 128 ÷ 64 division, while the fragment's only division is
`udiv`/`urem` at 64 ÷ 64 → 64.

`Verified/Montgomery.lean` and `Verified/Mont2.lean` remove that
obstruction: Montgomery reduction computes `x·y·R⁻¹ mod N` with **no
division at all**, and `Verified/Mont2.lean` realizes it at two limbs in
the fragment's own instruction set.  This module assembles the result into
a `Reflect.Program`.

## What the artifact checks

For a Proth number `N = k·2ⁿ + 1` and a witness `a`, Proth's criterion is

    N is prime  ⟺  ∃ a,  a^((N−1)/2) ≡ −1 (mod N)          (2ⁿ > k)

The producer *searches* for the witness `a` (that is what the reference's
Jacobi symbol is for); the **verifier** only has to check the congruence for
the witness it is handed.  So the Jacobi loop, the early exits and the
data-dependent trip counts listed as secondary obstructions in
`tg_goldbach.md` all disappear on the checking side: what remains is one
modular exponentiation, which is exactly what this program computes.

`prothProgram_denote` is the bridge: the program's denotation is `0` if and
only if `a^((N−1)/2) mod N = N − 1`.

Proth's criterion itself — that the congruence implies primality — is not
formalized here; it is a classical theorem (Proth 1878; Robinson,
*Math. Comp.* 11 (1957) 21–22) and is used, as elsewhere in this package, at
the level of the source development rather than inside Lean.  What is
formalized is the arithmetic, which is where the obstruction was.

## Shape

`k` and `a` are emission-time literals, so the Montgomery setup constants
(`N`'s limbs, the multiplier `n′`, `R mod N`, `a·R mod N`, and the
Montgomery form of `N − 1`) are literals too, and their defining properties
are closed decidable propositions the kernel checks instantly.  No
in-program setup loop is needed.

The exponent is `(N−1)/2 = k·2ⁿ⁻¹`, whose binary expansion is `k`'s bits
followed by `n−1` zeros.  The loop therefore runs `kbits + n − 1` times with
a *uniform* body: shift one bit out of a window register, square, and
multiply by `a` or by `1` selected branchlessly.  The trailing zero bits
multiply by the Montgomery `1`, which is a genuine no-op on the value, so
the loop stays branchless at the cost of `n−1` redundant multiplications.
-/

namespace LeanCompCert.Ports.TGProth

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

/-! ## Instruction-block generators

Every block below mirrors, statement for statement, the corresponding
definition in `Verified/Mont2.lean`, so its specification holds by
computation.  All register numbers are *concrete*: operands are passed as
register indices, never as `Operand` variables, because a symbolic operand
blocks the definitional reduction that makes each leaf specification a
one-line `rfl`.  Inputs are routed into the fixed registers `16 … 19` by
`mov`s at the call site, which costs four instructions per multiplication
and buys a single instantiation to reason about.
-/

/-- `Mont2.hlW` on registers `a`, `b`: the 128-bit product, shift-and-mask,
18 instructions.  `lo` lands at `o + 11`, `hi` at `o + 17`. -/
def hlB (o a b : Nat) : List Instr :=
  [ .binop (o + 0)  .band (.reg a) (.lit 4294967295)
  , .binop (o + 1)  .lshr (.reg a) (.lit 32)
  , .binop (o + 2)  .band (.reg b) (.lit 4294967295)
  , .binop (o + 3)  .lshr (.reg b) (.lit 32)
  , .binop (o + 4)  .mul  (.reg (o + 0)) (.reg (o + 2))
  , .binop (o + 5)  .mul  (.reg (o + 0)) (.reg (o + 3))
  , .binop (o + 6)  .mul  (.reg (o + 1)) (.reg (o + 2))
  , .binop (o + 7)  .mul  (.reg (o + 1)) (.reg (o + 3))
  , .binop (o + 8)  .add  (.reg (o + 5)) (.reg (o + 6))
  , .binop (o + 9)  .lt   (.reg (o + 8)) (.reg (o + 5))
  , .binop (o + 10) .shl  (.reg (o + 8)) (.lit 32)
  , .binop (o + 11) .add  (.reg (o + 4)) (.reg (o + 10))
  , .binop (o + 12) .lt   (.reg (o + 11)) (.reg (o + 4))
  , .binop (o + 13) .lshr (.reg (o + 8)) (.lit 32)
  , .binop (o + 14) .add  (.reg (o + 7)) (.reg (o + 13))
  , .binop (o + 15) .shl  (.reg (o + 9)) (.lit 32)
  , .binop (o + 16) .add  (.reg (o + 14)) (.reg (o + 15))
  , .binop (o + 17) .add  (.reg (o + 16)) (.reg (o + 12)) ]

/-- `Mont2.addcW x y c` with all three in registers: value at `o + 1`,
carry at `o + 4`. -/
def addcB (o x y c : Nat) : List Instr :=
  [ .binop (o + 0) .add (.reg x) (.reg y)
  , .binop (o + 1) .add (.reg (o + 0)) (.reg c)
  , .binop (o + 2) .lt  (.reg (o + 0)) (.reg x)
  , .binop (o + 3) .lt  (.reg (o + 1)) (.reg (o + 0))
  , .binop (o + 4) .add (.reg (o + 2)) (.reg (o + 3)) ]

/-- `Mont2.addcW x y 0`. -/
def addcB0 (o x y : Nat) : List Instr :=
  [ .binop (o + 0) .add (.reg x) (.reg y)
  , .binop (o + 1) .add (.reg (o + 0)) (.lit 0)
  , .binop (o + 2) .lt  (.reg (o + 0)) (.reg x)
  , .binop (o + 3) .lt  (.reg (o + 1)) (.reg (o + 0))
  , .binop (o + 4) .add (.reg (o + 2)) (.reg (o + 3)) ]

/-- `Mont2.addcW x 0 c` — the top-limb carry propagation. -/
def addcBz (o x c : Nat) : List Instr :=
  [ .binop (o + 0) .add (.reg x) (.lit 0)
  , .binop (o + 1) .add (.reg (o + 0)) (.reg c)
  , .binop (o + 2) .lt  (.reg (o + 0)) (.reg x)
  , .binop (o + 3) .lt  (.reg (o + 1)) (.reg (o + 0))
  , .binop (o + 4) .add (.reg (o + 2)) (.reg (o + 3)) ]

/-- `Mont2.sbbcW x y c`: value at `o + 1`, borrow at `o + 4`. -/
def sbbB (o x y c : Nat) : List Instr :=
  [ .binop (o + 0) .sub (.reg x) (.reg y)
  , .binop (o + 1) .sub (.reg (o + 0)) (.reg c)
  , .binop (o + 2) .lt  (.reg x) (.reg y)
  , .binop (o + 3) .lt  (.reg (o + 0)) (.reg c)
  , .binop (o + 4) .add (.reg (o + 2)) (.reg (o + 3)) ]

/-- `Mont2.sbbcW x y 0`. -/
def sbbB0 (o x y : Nat) : List Instr :=
  [ .binop (o + 0) .sub (.reg x) (.reg y)
  , .binop (o + 1) .sub (.reg (o + 0)) (.lit 0)
  , .binop (o + 2) .lt  (.reg x) (.reg y)
  , .binop (o + 3) .lt  (.reg (o + 0)) (.lit 0)
  , .binop (o + 4) .add (.reg (o + 2)) (.reg (o + 3)) ]

/-- `Mont2.wsel c a b`: result at `o + 3`.  Branchless — two
multiplications by a 0/1 flag, no comparison and no jump. -/
def selB (o c a b : Nat) : List Instr :=
  [ .binop (o + 0) .mul (.reg a) (.reg c)
  , .binop (o + 1) .sub (.lit 1) (.reg c)
  , .binop (o + 2) .mul (.reg b) (.reg (o + 1))
  , .binop (o + 3) .add (.reg (o + 0)) (.reg (o + 2)) ]

/-- `Mont2.condSub2`: results at `o + 14` and `o + 18`. -/
def csB (o n0 n1 x0 x1 : Nat) : List Instr :=
  sbbB0 (o + 0) x0 n0
    ++ sbbB (o + 5) x1 n1 (o + 4)
    ++ [ .binop (o + 10) .sub (.lit 1) (.reg (o + 9)) ]
    ++ selB (o + 11) (o + 10) (o + 1) x0
    ++ selB (o + 15) (o + 10) (o + 6) x1

/-- `Mont2.mul2`: the four limbs land at `o + 11`, `o + 85`, `o + 90`,
`o + 94`. -/
def mul2B (o a0 a1 b0 b1 : Nat) : List Instr :=
  hlB (o + 0) a0 b0
    ++ hlB (o + 18) a1 b0
    ++ addcB0 (o + 36) (o + 17) (o + 29)
    ++ [ .binop (o + 41) .add (.reg (o + 35)) (.reg (o + 40)) ]
    ++ hlB (o + 42) a0 b1
    ++ hlB (o + 60) a1 b1
    ++ addcB0 (o + 78) (o + 59) (o + 71)
    ++ [ .binop (o + 83) .add (.reg (o + 77)) (.reg (o + 82)) ]
    ++ addcB0 (o + 84) (o + 37) (o + 53)
    ++ addcB (o + 89) (o + 41) (o + 79) (o + 88)
    ++ [ .binop (o + 94) .add (.reg (o + 83)) (.reg (o + 93)) ]

/-- `Mont2.redcStep2`: the four limbs land at `o + 49`, `o + 54`, `o + 59`,
`o + 62`. -/
def redcB (o n0 n1 np t0 t1 t2 t3 : Nat) : List Instr :=
  [ .binop (o + 0) .mul (.reg t0) (.reg np) ]
    ++ hlB (o + 1) (o + 0) n0
    ++ hlB (o + 19) (o + 0) n1
    ++ addcB0 (o + 37) (o + 18) (o + 30)
    ++ [ .binop (o + 42) .add (.reg (o + 36)) (.reg (o + 41)) ]
    ++ addcB0 (o + 43) t0 (o + 12)
    ++ addcB (o + 48) t1 (o + 38) (o + 47)
    ++ addcB (o + 53) t2 (o + 42) (o + 52)
    ++ addcBz (o + 58) t3 (o + 57)

/-- Base register of the Montgomery-multiply scratch region. -/
def SC : Nat := 32

/--
`Mont2.montMul2` as a closed instruction block: reads `N`'s limbs from
registers `2`, `3`, the multiplier from `4`, and the two operands from
`16, 17` and `18, 19`; writes the result to `267` and `271`, using
`32 … 271` as scratch.  240 instructions, no division.
-/
def mmBlock : List Instr :=
  mul2B (SC + 0) 16 17 18 19
    ++ redcB (SC + 95) 2 3 4 (SC + 11) (SC + 85) (SC + 90) (SC + 94)
    ++ redcB (SC + 158) 2 3 4 (SC + 144) (SC + 149) (SC + 154) (SC + 157)
    ++ csB (SC + 221) 2 3 (SC + 207) (SC + 212)

/-- Low result limb of `mmBlock`. -/
def mmLo : Nat := SC + 235
/-- High result limb of `mmBlock`. -/
def mmHi : Nat := SC + 239

/-- Route two limbs into the multiplier's fixed operand registers. -/
def loadA (a0 a1 : Nat) : List Instr := [ .mov 16 (.reg a0), .mov 17 (.reg a1) ]
/-- Route two limbs into the multiplier's second operand registers. -/
def loadB (b0 b1 : Nat) : List Instr := [ .mov 18 (.reg b0), .mov 19 (.reg b1) ]
/-- Move the multiplier's result out. -/
def storeC (c0 c1 : Nat) : List Instr :=
  [ .mov c0 (.reg mmLo), .mov c1 (.reg mmHi) ]

/-! ## Register map

| register | contents |
|---|---|
| `0` | output: `0` if the witness certifies, `1` otherwise |
| `1` | `w`, the exponent-bit window |
| `2`, `3` | `N`'s limbs |
| `4` | the Montgomery multiplier `n′` |
| `5`, `6` | the accumulator, in Montgomery form |
| `7`, `8` | `a·R mod N` |
| `9`, `10` | `R mod N` (the Montgomery `1`) |
| `11`, `12` | `(N−1)·R mod N` (the target) |
| `13` | the current exponent bit |
| `14`, `15` | the selected multiplier |
| `22 … 30` | body scratch |
| `32 … 271` | Montgomery-multiply scratch |
-/

/-- Number of registers the program declares. -/
def regCount : Nat := 272

/-! ## Setup constants

All computed from the emission-time literals `n`, `k`, `a`; each is a `Nat`
the kernel evaluates in microseconds.
-/

/-- The Proth number `k·2ⁿ + 1`. -/
def prothN (n k : Nat) : Nat := k * 2 ^ n + 1

/-- The Montgomery radix at two limbs. -/
def RR : Nat := 2 ^ 128

def n0Of (n k : Nat) : Nat := prothN n k % 2 ^ 64
def n1Of (n k : Nat) : Nat := prothN n k / 2 ^ 64

/-- The Montgomery multiplier in closed form: for `N = k·2ⁿ + 1` with
`n ≥ 32`, `n′ = k·2ⁿ − 1` works, because `N·n′ + 1 = (k·2ⁿ)²` is divisible
by `2⁶⁴`.  No Newton iteration. -/
def npOf (n k : Nat) : Nat := (k * 2 ^ n + (2 ^ 64 - 1)) % 2 ^ 64

def oneOf (n k : Nat) : Nat := RR % prothN n k
def abarOf (n k a : Nat) : Nat := a * RR % prothN n k
def tgtOf (n k : Nat) : Nat := prothN n k - oneOf n k

/-! ## The program -/

/-- Init: load the setup literals; the accumulator starts at the Montgomery
`1` and the window at `k`. -/
def initInstrs (n k a : Nat) : List Instr :=
  [ .mov 1 (.lit k)
  , .mov 2 (.lit (n0Of n k))
  , .mov 3 (.lit (n1Of n k))
  , .mov 4 (.lit (npOf n k))
  , .mov 5 (.lit (oneOf n k % 2 ^ 64))
  , .mov 6 (.lit (oneOf n k / 2 ^ 64))
  , .mov 7 (.lit (abarOf n k a % 2 ^ 64))
  , .mov 8 (.lit (abarOf n k a / 2 ^ 64))
  , .mov 9 (.lit (oneOf n k % 2 ^ 64))
  , .mov 10 (.lit (oneOf n k / 2 ^ 64))
  , .mov 11 (.lit (tgtOf n k % 2 ^ 64))
  , .mov 12 (.lit (tgtOf n k / 2 ^ 64)) ]

/-- One square-and-multiply step: peel a bit off the window, square the
accumulator, and multiply by `a` or by `1` — selected branchlessly. -/
def bodyHead (kbits : Nat) : List Instr :=
  [ .binop 13 .lshr (.reg 1) (.lit (kbits - 1))
  , .binop 22 .shl  (.reg 1) (.lit 1)
  , .binop 1  .band (.reg 22) (.lit (2 ^ kbits - 1)) ]

/-- The part of the body that does not depend on `kbits`: select the
multiplier, square, multiply. -/
def bodyTail : List Instr :=
  selB 23 13 7 9
    ++ selB 27 13 8 10
    ++ [ .mov 14 (.reg 26), .mov 15 (.reg 30) ]
    ++ loadA 5 6 ++ loadB 5 6 ++ mmBlock ++ storeC 5 6
    ++ loadA 5 6 ++ loadB 14 15 ++ mmBlock ++ storeC 5 6

def bodyInstrs (kbits : Nat) : List Instr := bodyHead kbits ++ bodyTail

/-- Epilogue: compare the accumulator with the Montgomery form of `N − 1`.
The output is `0` exactly on agreement — the artifact's exit-code contract. -/
def epiInstrs : List Instr :=
  [ .binop 22 .eq   (.reg 5) (.reg 11)
  , .binop 23 .eq   (.reg 6) (.reg 12)
  , .binop 24 .band (.reg 22) (.reg 23)
  , .binop 0  .sub  (.lit 1) (.reg 24) ]

/--
The Proth-test program for `N = k·2ⁿ + 1` with witness `a`, where `k` is
known to fit in `kbits` bits.  One loop, uniform body, no memory.
-/
def prothProgram (n kbits k a : Nat) : Program := {
  regCount := regCount
  loopCount := kbits + (n - 1)
  init := initInstrs n k a
  body := bodyInstrs kbits
  epilogue := epiInstrs
  output := 0
}

/-! ## Emission -/

/-- Rolled C for the Proth test: the loop body is emitted once, so the
artifact's size is independent of the exponent length. -/
def emitProth (n kbits k a : Nat) (name : String) :
    Except (Array String) String :=
  emitRolled (prothProgram n kbits k a) name



/-! ## Block plumbing

Reasoning about a 505-instruction body never unfolds it: leaf blocks have
one-line `rfl` specifications, and `srun_append` glues them.  The frame
facts are decidable and block-sized.
-/

/-- Every register the block writes is at or above `lo`. -/
def WritesAbove (lo : Nat) (b : List Instr) : Prop := ∀ i ∈ b, lo ≤ sdest i

instance (lo : Nat) (b : List Instr) : Decidable (WritesAbove lo b) := by
  unfold WritesAbove; infer_instance

/-- A block that writes only at or above `lo` leaves everything below it. -/
theorem srun_below (k lo : Nat) (b : List Instr) (h : WritesAbove lo b)
    (s : RegState) (r : Nat) (hr : r < lo) : srun k s b r = s r :=
  srun_untouched k r b (fun i hi => by have := h i hi; omega) s

set_option maxRecDepth 40000

/-! ### Leaf-block specifications

Each is an instant `rfl`: the register numbers are concrete, so `srun`
reduces definitionally to the corresponding `Mont2` word function.  The one
exception is the low limb of `sbbB0`, where `M - (0 % M)` would force the
kernel to add a symbolic register to a `2⁶⁴`-sized literal; there the
literal is normalized by rewriting instead.
-/

theorem denoteOp_sub_getD (a b : Nat) :
    (Reflect.denoteOp .sub a b).getD 0 = Mont2.wsub a b := rfl

theorem denoteOperand_lit_zero (k : Nat) (s : RegState) :
    Reflect.denoteOperand k s (Operand.lit 0) = 0 := by
  show (0 : Nat) % M = 0
  exact Nat.zero_mod _

theorem lf1 (k : Nat) (s : RegState) :
    srun k s (hlB 32 16 18) 43 = (Mont2.hlW (s 16) (s 18)).1 := rfl

theorem lf2 (k : Nat) (s : RegState) :
    srun k s (hlB 32 16 18) 49 = (Mont2.hlW (s 16) (s 18)).2 := rfl

theorem lf3 (k : Nat) (s : RegState) :
    srun k s (hlB 50 17 18) 61 = (Mont2.hlW (s 17) (s 18)).1 := rfl

theorem lf4 (k : Nat) (s : RegState) :
    srun k s (hlB 50 17 18) 67 = (Mont2.hlW (s 17) (s 18)).2 := rfl

theorem lf5 (k : Nat) (s : RegState) :
    srun k s (addcB0 68 49 61) 69 = (Mont2.addcW (s 49) (s 61) 0).1 := rfl

theorem lf6 (k : Nat) (s : RegState) :
    srun k s (addcB0 68 49 61) 72 = (Mont2.addcW (s 49) (s 61) 0).2 := rfl

theorem lf7 (k : Nat) (s : RegState) :
    srun k s ([ .binop 73 .add (.reg 67) (.reg 72) ]) 73 = Mont2.wadd (s 67) (s 72) := rfl

theorem lf8 (k : Nat) (s : RegState) :
    srun k s (hlB 74 16 19) 85 = (Mont2.hlW (s 16) (s 19)).1 := rfl

theorem lf9 (k : Nat) (s : RegState) :
    srun k s (hlB 74 16 19) 91 = (Mont2.hlW (s 16) (s 19)).2 := rfl

theorem lf10 (k : Nat) (s : RegState) :
    srun k s (hlB 92 17 19) 103 = (Mont2.hlW (s 17) (s 19)).1 := rfl

theorem lf11 (k : Nat) (s : RegState) :
    srun k s (hlB 92 17 19) 109 = (Mont2.hlW (s 17) (s 19)).2 := rfl

theorem lf12 (k : Nat) (s : RegState) :
    srun k s (addcB0 110 91 103) 111 = (Mont2.addcW (s 91) (s 103) 0).1 := rfl

theorem lf13 (k : Nat) (s : RegState) :
    srun k s (addcB0 110 91 103) 114 = (Mont2.addcW (s 91) (s 103) 0).2 := rfl

theorem lf14 (k : Nat) (s : RegState) :
    srun k s ([ .binop 115 .add (.reg 109) (.reg 114) ]) 115 = Mont2.wadd (s 109) (s 114) := rfl

theorem lf15 (k : Nat) (s : RegState) :
    srun k s (addcB0 116 69 85) 117 = (Mont2.addcW (s 69) (s 85) 0).1 := rfl

theorem lf16 (k : Nat) (s : RegState) :
    srun k s (addcB0 116 69 85) 120 = (Mont2.addcW (s 69) (s 85) 0).2 := rfl

theorem lf17 (k : Nat) (s : RegState) :
    srun k s (addcB 121 73 111 120) 122 = (Mont2.addcW (s 73) (s 111) (s 120)).1 := rfl

theorem lf18 (k : Nat) (s : RegState) :
    srun k s (addcB 121 73 111 120) 125 = (Mont2.addcW (s 73) (s 111) (s 120)).2 := rfl

theorem lf19 (k : Nat) (s : RegState) :
    srun k s ([ .binop 126 .add (.reg 115) (.reg 125) ]) 126 = Mont2.wadd (s 115) (s 125) := rfl

theorem lf20 (k : Nat) (s : RegState) :
    srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) 127 = Mont2.wmul (s 43) (s 4) := rfl

theorem lf21 (k : Nat) (s : RegState) :
    srun k s (hlB 128 127 2) 139 = (Mont2.hlW (s 127) (s 2)).1 := rfl

theorem lf22 (k : Nat) (s : RegState) :
    srun k s (hlB 128 127 2) 145 = (Mont2.hlW (s 127) (s 2)).2 := rfl

theorem lf23 (k : Nat) (s : RegState) :
    srun k s (hlB 146 127 3) 157 = (Mont2.hlW (s 127) (s 3)).1 := rfl

theorem lf24 (k : Nat) (s : RegState) :
    srun k s (hlB 146 127 3) 163 = (Mont2.hlW (s 127) (s 3)).2 := rfl

theorem lf25 (k : Nat) (s : RegState) :
    srun k s (addcB0 164 145 157) 165 = (Mont2.addcW (s 145) (s 157) 0).1 := rfl

theorem lf26 (k : Nat) (s : RegState) :
    srun k s (addcB0 164 145 157) 168 = (Mont2.addcW (s 145) (s 157) 0).2 := rfl

theorem lf27 (k : Nat) (s : RegState) :
    srun k s ([ .binop 169 .add (.reg 163) (.reg 168) ]) 169 = Mont2.wadd (s 163) (s 168) := rfl

theorem lf28 (k : Nat) (s : RegState) :
    srun k s (addcB0 170 43 139) 174 = (Mont2.addcW (s 43) (s 139) 0).2 := rfl

theorem lf29 (k : Nat) (s : RegState) :
    srun k s (addcB 175 117 165 174) 176 = (Mont2.addcW (s 117) (s 165) (s 174)).1 := rfl

theorem lf30 (k : Nat) (s : RegState) :
    srun k s (addcB 175 117 165 174) 179 = (Mont2.addcW (s 117) (s 165) (s 174)).2 := rfl

theorem lf31 (k : Nat) (s : RegState) :
    srun k s (addcB 180 122 169 179) 181 = (Mont2.addcW (s 122) (s 169) (s 179)).1 := rfl

theorem lf32 (k : Nat) (s : RegState) :
    srun k s (addcB 180 122 169 179) 184 = (Mont2.addcW (s 122) (s 169) (s 179)).2 := rfl

theorem lf33 (k : Nat) (s : RegState) :
    srun k s (addcBz 185 126 184) 186 = (Mont2.addcW (s 126) 0 (s 184)).1 := rfl

theorem lf34 (k : Nat) (s : RegState) :
    srun k s (addcBz 185 126 184) 189 = (Mont2.addcW (s 126) 0 (s 184)).2 := rfl

theorem lf35 (k : Nat) (s : RegState) :
    srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) 190 = Mont2.wmul (s 176) (s 4) := rfl

theorem lf36 (k : Nat) (s : RegState) :
    srun k s (hlB 191 190 2) 202 = (Mont2.hlW (s 190) (s 2)).1 := rfl

theorem lf37 (k : Nat) (s : RegState) :
    srun k s (hlB 191 190 2) 208 = (Mont2.hlW (s 190) (s 2)).2 := rfl

theorem lf38 (k : Nat) (s : RegState) :
    srun k s (hlB 209 190 3) 220 = (Mont2.hlW (s 190) (s 3)).1 := rfl

theorem lf39 (k : Nat) (s : RegState) :
    srun k s (hlB 209 190 3) 226 = (Mont2.hlW (s 190) (s 3)).2 := rfl

theorem lf40 (k : Nat) (s : RegState) :
    srun k s (addcB0 227 208 220) 228 = (Mont2.addcW (s 208) (s 220) 0).1 := rfl

theorem lf41 (k : Nat) (s : RegState) :
    srun k s (addcB0 227 208 220) 231 = (Mont2.addcW (s 208) (s 220) 0).2 := rfl

theorem lf42 (k : Nat) (s : RegState) :
    srun k s ([ .binop 232 .add (.reg 226) (.reg 231) ]) 232 = Mont2.wadd (s 226) (s 231) := rfl

theorem lf43 (k : Nat) (s : RegState) :
    srun k s (addcB0 233 176 202) 237 = (Mont2.addcW (s 176) (s 202) 0).2 := rfl

theorem lf44 (k : Nat) (s : RegState) :
    srun k s (addcB 238 181 228 237) 239 = (Mont2.addcW (s 181) (s 228) (s 237)).1 := rfl

theorem lf45 (k : Nat) (s : RegState) :
    srun k s (addcB 238 181 228 237) 242 = (Mont2.addcW (s 181) (s 228) (s 237)).2 := rfl

theorem lf46 (k : Nat) (s : RegState) :
    srun k s (addcB 243 186 232 242) 244 = (Mont2.addcW (s 186) (s 232) (s 242)).1 := rfl

theorem lf47 (k : Nat) (s : RegState) :
    srun k s (addcB 243 186 232 242) 247 = (Mont2.addcW (s 186) (s 232) (s 242)).2 := rfl

theorem lf48 (k : Nat) (s : RegState) :
    srun k s (addcBz 248 189 247) 249 = (Mont2.addcW (s 189) 0 (s 247)).1 := rfl

theorem lf49 (k : Nat) (s : RegState) :
    srun k s (addcBz 248 189 247) 252 = (Mont2.addcW (s 189) 0 (s 247)).2 := rfl

theorem lf50 (k : Nat) (s : RegState) :
    srun k s (sbbB0 253 239 2) 254 = (Mont2.sbbcW (s 239) (s 2) 0).1 := by
  have q1 : srun k s (sbbB0 253 239 2) 254
      = (Reflect.denoteOp .sub ((Reflect.denoteOp .sub (s 239) (s 2)).getD 0)
          (Reflect.denoteOperand k s (Operand.lit 0))).getD 0 := rfl
  rw [q1, denoteOperand_lit_zero, denoteOp_sub_getD, denoteOp_sub_getD]
  rfl

theorem lf51 (k : Nat) (s : RegState) :
    srun k s (sbbB0 253 239 2) 257 = (Mont2.sbbcW (s 239) (s 2) 0).2 := rfl

theorem lf52 (k : Nat) (s : RegState) :
    srun k s (sbbB 258 244 3 257) 259 = (Mont2.sbbcW (s 244) (s 3) (s 257)).1 := rfl

theorem lf53 (k : Nat) (s : RegState) :
    srun k s (sbbB 258 244 3 257) 262 = (Mont2.sbbcW (s 244) (s 3) (s 257)).2 := rfl

theorem lf54 (k : Nat) (s : RegState) :
    srun k s ([ .binop 263 .sub (.lit 1) (.reg 262) ]) 263 = Mont2.wsub 1 (s 262) := rfl

theorem lf55 (k : Nat) (s : RegState) :
    srun k s (selB 264 263 254 239) 267 = Mont2.wsel (s 263) (s 254) (s 239) := rfl

theorem lf56 (k : Nat) (s : RegState) :
    srun k s (selB 268 263 259 244) 271 = Mont2.wsel (s 263) (s 259) (s 244) := rfl

theorem lf57 (k : Nat) (s : RegState) :
    srun k s (selB 23 13 7 9) 26 = Mont2.wsel (s 13) (s 7) (s 9) := rfl

theorem lf58 (k : Nat) (s : RegState) :
    srun k s (selB 27 13 8 10) 30 = Mont2.wsel (s 13) (s 8) (s 10) := rfl

theorem lf59 (k : Nat) (s : RegState) :
    srun k s ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 14 = s 26 := rfl

theorem lf60 (k : Nat) (s : RegState) :
    srun k s ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 15 = s 30 := rfl

theorem lf61 (k : Nat) (s : RegState) :
    srun k s (loadA 5 6) 16 = s 5 := rfl

theorem lf62 (k : Nat) (s : RegState) :
    srun k s (loadA 5 6) 17 = s 6 := rfl

theorem lf63 (k : Nat) (s : RegState) :
    srun k s (loadB 5 6) 18 = s 5 := rfl

theorem lf64 (k : Nat) (s : RegState) :
    srun k s (loadB 5 6) 19 = s 6 := rfl

theorem lf65 (k : Nat) (s : RegState) :
    srun k s (storeC 5 6) 5 = s 267 := rfl

theorem lf66 (k : Nat) (s : RegState) :
    srun k s (storeC 5 6) 6 = s 271 := rfl

theorem lf67 (k : Nat) (s : RegState) :
    srun k s (loadB 14 15) 18 = s 14 := rfl

theorem lf68 (k : Nat) (s : RegState) :
    srun k s (loadB 14 15) 19 = s 15 := rfl

theorem mul2B_spec (k : Nat) (s : RegState) :
    srun k s (mul2B 32 16 17 18 19) 43 = (Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1 ∧
      srun k s (mul2B 32 16 17 18 19) 117 = (Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1 ∧
      srun k s (mul2B 32 16 17 18 19) 122 = (Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1 ∧
      srun k s (mul2B 32 16 17 18 19) 126 = (Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2 := by
  have hsplit : mul2B 32 16 17 18 19 =
      hlB 32 16 18
        ++ hlB 50 17 18
        ++ addcB0 68 49 61
        ++ [ .binop 73 .add (.reg 67) (.reg 72) ]
        ++ hlB 74 16 19
        ++ hlB 92 17 19
        ++ addcB0 110 91 103
        ++ [ .binop 115 .add (.reg 109) (.reg 114) ]
        ++ addcB0 116 69 85
        ++ addcB 121 73 111 120
        ++ [ .binop 126 .add (.reg 115) (.reg 125) ] := rfl
  rw [hsplit]
  simp only [srun_append]
  have fr0 : ∀ r, r < 32 → srun k s (hlB 32 16 18) r = s r :=
    fun r hr => srun_below k 32 (hlB 32 16 18) (by decide +kernel) s r hr
  have hc0_16 : srun k s (hlB 32 16 18) 16 = s 16 :=
    fr0 16 (by omega)
  have hc0_17 : srun k s (hlB 32 16 18) 17 = s 17 :=
    fr0 17 (by omega)
  have hc0_18 : srun k s (hlB 32 16 18) 18 = s 18 :=
    fr0 18 (by omega)
  have hc0_19 : srun k s (hlB 32 16 18) 19 = s 19 :=
    fr0 19 (by omega)
  have ho0_43 : srun k s (hlB 32 16 18) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [lf1 k s]
  have ho0_49 : srun k s (hlB 32 16 18) 49 = (Mont2.hlW (s 16) (s 18)).2 := by
    rw [lf2 k s]
  clear fr0
  generalize hg0 : srun k s (hlB 32 16 18) = t1 at hc0_16 hc0_17 hc0_18 hc0_19 ho0_43 ho0_49 ⊢
  clear hg0
  have fr1 : ∀ r, r < 50 → srun k t1 (hlB 50 17 18) r = t1 r :=
    fun r hr => srun_below k 50 (hlB 50 17 18) (by decide +kernel) t1 r hr
  have hc0_16a : srun k t1 (hlB 50 17 18) 16 = s 16 := by
    rw [fr1 16 (by omega)]; exact hc0_16
  have hc0_17a : srun k t1 (hlB 50 17 18) 17 = s 17 := by
    rw [fr1 17 (by omega)]; exact hc0_17
  have hc0_19a : srun k t1 (hlB 50 17 18) 19 = s 19 := by
    rw [fr1 19 (by omega)]; exact hc0_19
  have ho0_43a : srun k t1 (hlB 50 17 18) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr1 43 (by omega)]; exact ho0_43
  have ho0_49a : srun k t1 (hlB 50 17 18) 49 = (Mont2.hlW (s 16) (s 18)).2 := by
    rw [fr1 49 (by omega)]; exact ho0_49
  have ho1_61 : srun k t1 (hlB 50 17 18) 61 = (Mont2.hlW (s 17) (s 18)).1 := by
    rw [lf3 k t1, hc0_17, hc0_18]
  have ho1_67 : srun k t1 (hlB 50 17 18) 67 = (Mont2.hlW (s 17) (s 18)).2 := by
    rw [lf4 k t1, hc0_17, hc0_18]
  clear fr1 hc0_16 hc0_17 hc0_18 hc0_19 ho0_43 ho0_49
  generalize hg1 : srun k t1 (hlB 50 17 18) = t2 at hc0_16a hc0_17a hc0_19a ho0_43a ho0_49a ho1_61 ho1_67 ⊢
  clear hg1
  have fr2 : ∀ r, r < 68 → srun k t2 (addcB0 68 49 61) r = t2 r :=
    fun r hr => srun_below k 68 (addcB0 68 49 61) (by decide +kernel) t2 r hr
  have hc0_16aa : srun k t2 (addcB0 68 49 61) 16 = s 16 := by
    rw [fr2 16 (by omega)]; exact hc0_16a
  have hc0_17aa : srun k t2 (addcB0 68 49 61) 17 = s 17 := by
    rw [fr2 17 (by omega)]; exact hc0_17a
  have hc0_19aa : srun k t2 (addcB0 68 49 61) 19 = s 19 := by
    rw [fr2 19 (by omega)]; exact hc0_19a
  have ho0_43aa : srun k t2 (addcB0 68 49 61) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr2 43 (by omega)]; exact ho0_43a
  have ho1_67a : srun k t2 (addcB0 68 49 61) 67 = (Mont2.hlW (s 17) (s 18)).2 := by
    rw [fr2 67 (by omega)]; exact ho1_67
  have ho2_69 : srun k t2 (addcB0 68 49 61) 69 = (Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1 := by
    rw [lf5 k t2, ho0_49a, ho1_61]
  have ho2_72 : srun k t2 (addcB0 68 49 61) 72 = (Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2 := by
    rw [lf6 k t2, ho0_49a, ho1_61]
  clear fr2 hc0_16a hc0_17a hc0_19a ho0_43a ho0_49a ho1_61 ho1_67
  generalize hg2 : srun k t2 (addcB0 68 49 61) = t3 at hc0_16aa hc0_17aa hc0_19aa ho0_43aa ho1_67a ho2_69 ho2_72 ⊢
  clear hg2
  have fr3 : ∀ r, r < 73 → srun k t3 ([ .binop 73 .add (.reg 67) (.reg 72) ]) r = t3 r :=
    fun r hr => srun_below k 73 ([ .binop 73 .add (.reg 67) (.reg 72) ]) (by decide +kernel) t3 r hr
  have hc0_16aaa : srun k t3 ([ .binop 73 .add (.reg 67) (.reg 72) ]) 16 = s 16 := by
    rw [fr3 16 (by omega)]; exact hc0_16aa
  have hc0_17aaa : srun k t3 ([ .binop 73 .add (.reg 67) (.reg 72) ]) 17 = s 17 := by
    rw [fr3 17 (by omega)]; exact hc0_17aa
  have hc0_19aaa : srun k t3 ([ .binop 73 .add (.reg 67) (.reg 72) ]) 19 = s 19 := by
    rw [fr3 19 (by omega)]; exact hc0_19aa
  have ho0_43aaa : srun k t3 ([ .binop 73 .add (.reg 67) (.reg 72) ]) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr3 43 (by omega)]; exact ho0_43aa
  have ho2_69a : srun k t3 ([ .binop 73 .add (.reg 67) (.reg 72) ]) 69 = (Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1 := by
    rw [fr3 69 (by omega)]; exact ho2_69
  have ho3_73 : srun k t3 ([ .binop 73 .add (.reg 67) (.reg 72) ]) 73 = Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2) := by
    rw [lf7 k t3, ho1_67a, ho2_72]
  clear fr3 hc0_16aa hc0_17aa hc0_19aa ho0_43aa ho1_67a ho2_69 ho2_72
  generalize hg3 : srun k t3 ([ .binop 73 .add (.reg 67) (.reg 72) ]) = t4 at hc0_16aaa hc0_17aaa hc0_19aaa ho0_43aaa ho2_69a ho3_73 ⊢
  clear hg3
  have fr4 : ∀ r, r < 74 → srun k t4 (hlB 74 16 19) r = t4 r :=
    fun r hr => srun_below k 74 (hlB 74 16 19) (by decide +kernel) t4 r hr
  have hc0_17aaaa : srun k t4 (hlB 74 16 19) 17 = s 17 := by
    rw [fr4 17 (by omega)]; exact hc0_17aaa
  have hc0_19aaaa : srun k t4 (hlB 74 16 19) 19 = s 19 := by
    rw [fr4 19 (by omega)]; exact hc0_19aaa
  have ho0_43aaaa : srun k t4 (hlB 74 16 19) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr4 43 (by omega)]; exact ho0_43aaa
  have ho2_69aa : srun k t4 (hlB 74 16 19) 69 = (Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1 := by
    rw [fr4 69 (by omega)]; exact ho2_69a
  have ho3_73a : srun k t4 (hlB 74 16 19) 73 = Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2) := by
    rw [fr4 73 (by omega)]; exact ho3_73
  have ho4_85 : srun k t4 (hlB 74 16 19) 85 = (Mont2.hlW (s 16) (s 19)).1 := by
    rw [lf8 k t4, hc0_16aaa, hc0_19aaa]
  have ho4_91 : srun k t4 (hlB 74 16 19) 91 = (Mont2.hlW (s 16) (s 19)).2 := by
    rw [lf9 k t4, hc0_16aaa, hc0_19aaa]
  clear fr4 hc0_16aaa hc0_17aaa hc0_19aaa ho0_43aaa ho2_69a ho3_73
  generalize hg4 : srun k t4 (hlB 74 16 19) = t5 at hc0_17aaaa hc0_19aaaa ho0_43aaaa ho2_69aa ho3_73a ho4_85 ho4_91 ⊢
  clear hg4
  have fr5 : ∀ r, r < 92 → srun k t5 (hlB 92 17 19) r = t5 r :=
    fun r hr => srun_below k 92 (hlB 92 17 19) (by decide +kernel) t5 r hr
  have ho0_43aaaaa : srun k t5 (hlB 92 17 19) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr5 43 (by omega)]; exact ho0_43aaaa
  have ho2_69aaa : srun k t5 (hlB 92 17 19) 69 = (Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1 := by
    rw [fr5 69 (by omega)]; exact ho2_69aa
  have ho3_73aa : srun k t5 (hlB 92 17 19) 73 = Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2) := by
    rw [fr5 73 (by omega)]; exact ho3_73a
  have ho4_85a : srun k t5 (hlB 92 17 19) 85 = (Mont2.hlW (s 16) (s 19)).1 := by
    rw [fr5 85 (by omega)]; exact ho4_85
  have ho4_91a : srun k t5 (hlB 92 17 19) 91 = (Mont2.hlW (s 16) (s 19)).2 := by
    rw [fr5 91 (by omega)]; exact ho4_91
  have ho5_103 : srun k t5 (hlB 92 17 19) 103 = (Mont2.hlW (s 17) (s 19)).1 := by
    rw [lf10 k t5, hc0_17aaaa, hc0_19aaaa]
  have ho5_109 : srun k t5 (hlB 92 17 19) 109 = (Mont2.hlW (s 17) (s 19)).2 := by
    rw [lf11 k t5, hc0_17aaaa, hc0_19aaaa]
  clear fr5 hc0_17aaaa hc0_19aaaa ho0_43aaaa ho2_69aa ho3_73a ho4_85 ho4_91
  generalize hg5 : srun k t5 (hlB 92 17 19) = t6 at ho0_43aaaaa ho2_69aaa ho3_73aa ho4_85a ho4_91a ho5_103 ho5_109 ⊢
  clear hg5
  have fr6 : ∀ r, r < 110 → srun k t6 (addcB0 110 91 103) r = t6 r :=
    fun r hr => srun_below k 110 (addcB0 110 91 103) (by decide +kernel) t6 r hr
  have ho0_43aaaaaa : srun k t6 (addcB0 110 91 103) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr6 43 (by omega)]; exact ho0_43aaaaa
  have ho2_69aaaa : srun k t6 (addcB0 110 91 103) 69 = (Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1 := by
    rw [fr6 69 (by omega)]; exact ho2_69aaa
  have ho3_73aaa : srun k t6 (addcB0 110 91 103) 73 = Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2) := by
    rw [fr6 73 (by omega)]; exact ho3_73aa
  have ho4_85aa : srun k t6 (addcB0 110 91 103) 85 = (Mont2.hlW (s 16) (s 19)).1 := by
    rw [fr6 85 (by omega)]; exact ho4_85a
  have ho5_109a : srun k t6 (addcB0 110 91 103) 109 = (Mont2.hlW (s 17) (s 19)).2 := by
    rw [fr6 109 (by omega)]; exact ho5_109
  have ho6_111 : srun k t6 (addcB0 110 91 103) 111 = (Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).1 := by
    rw [lf12 k t6, ho4_91a, ho5_103]
  have ho6_114 : srun k t6 (addcB0 110 91 103) 114 = (Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).2 := by
    rw [lf13 k t6, ho4_91a, ho5_103]
  clear fr6 ho0_43aaaaa ho2_69aaa ho3_73aa ho4_85a ho4_91a ho5_103 ho5_109
  generalize hg6 : srun k t6 (addcB0 110 91 103) = t7 at ho0_43aaaaaa ho2_69aaaa ho3_73aaa ho4_85aa ho5_109a ho6_111 ho6_114 ⊢
  clear hg6
  have fr7 : ∀ r, r < 115 → srun k t7 ([ .binop 115 .add (.reg 109) (.reg 114) ]) r = t7 r :=
    fun r hr => srun_below k 115 ([ .binop 115 .add (.reg 109) (.reg 114) ]) (by decide +kernel) t7 r hr
  have ho0_43aaaaaaa : srun k t7 ([ .binop 115 .add (.reg 109) (.reg 114) ]) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr7 43 (by omega)]; exact ho0_43aaaaaa
  have ho2_69aaaaa : srun k t7 ([ .binop 115 .add (.reg 109) (.reg 114) ]) 69 = (Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1 := by
    rw [fr7 69 (by omega)]; exact ho2_69aaaa
  have ho3_73aaaa : srun k t7 ([ .binop 115 .add (.reg 109) (.reg 114) ]) 73 = Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2) := by
    rw [fr7 73 (by omega)]; exact ho3_73aaa
  have ho4_85aaa : srun k t7 ([ .binop 115 .add (.reg 109) (.reg 114) ]) 85 = (Mont2.hlW (s 16) (s 19)).1 := by
    rw [fr7 85 (by omega)]; exact ho4_85aa
  have ho6_111a : srun k t7 ([ .binop 115 .add (.reg 109) (.reg 114) ]) 111 = (Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).1 := by
    rw [fr7 111 (by omega)]; exact ho6_111
  have ho7_115 : srun k t7 ([ .binop 115 .add (.reg 109) (.reg 114) ]) 115 = Mont2.wadd ((Mont2.hlW (s 17) (s 19)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).2) := by
    rw [lf14 k t7, ho5_109a, ho6_114]
  clear fr7 ho0_43aaaaaa ho2_69aaaa ho3_73aaa ho4_85aa ho5_109a ho6_111 ho6_114
  generalize hg7 : srun k t7 ([ .binop 115 .add (.reg 109) (.reg 114) ]) = t8 at ho0_43aaaaaaa ho2_69aaaaa ho3_73aaaa ho4_85aaa ho6_111a ho7_115 ⊢
  clear hg7
  have fr8 : ∀ r, r < 116 → srun k t8 (addcB0 116 69 85) r = t8 r :=
    fun r hr => srun_below k 116 (addcB0 116 69 85) (by decide +kernel) t8 r hr
  have ho0_43aaaaaaaa : srun k t8 (addcB0 116 69 85) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr8 43 (by omega)]; exact ho0_43aaaaaaa
  have ho3_73aaaaa : srun k t8 (addcB0 116 69 85) 73 = Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2) := by
    rw [fr8 73 (by omega)]; exact ho3_73aaaa
  have ho6_111aa : srun k t8 (addcB0 116 69 85) 111 = (Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).1 := by
    rw [fr8 111 (by omega)]; exact ho6_111a
  have ho7_115a : srun k t8 (addcB0 116 69 85) 115 = Mont2.wadd ((Mont2.hlW (s 17) (s 19)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).2) := by
    rw [fr8 115 (by omega)]; exact ho7_115
  have ho8_117 : srun k t8 (addcB0 116 69 85) 117 = (Mont2.addcW ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1) ((Mont2.hlW (s 16) (s 19)).1) 0).1 := by
    rw [lf15 k t8, ho2_69aaaaa, ho4_85aaa]
  have ho8_120 : srun k t8 (addcB0 116 69 85) 120 = (Mont2.addcW ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1) ((Mont2.hlW (s 16) (s 19)).1) 0).2 := by
    rw [lf16 k t8, ho2_69aaaaa, ho4_85aaa]
  clear fr8 ho0_43aaaaaaa ho2_69aaaaa ho3_73aaaa ho4_85aaa ho6_111a ho7_115
  generalize hg8 : srun k t8 (addcB0 116 69 85) = t9 at ho0_43aaaaaaaa ho3_73aaaaa ho6_111aa ho7_115a ho8_117 ho8_120 ⊢
  clear hg8
  have fr9 : ∀ r, r < 121 → srun k t9 (addcB 121 73 111 120) r = t9 r :=
    fun r hr => srun_below k 121 (addcB 121 73 111 120) (by decide +kernel) t9 r hr
  have ho0_43aaaaaaaaa : srun k t9 (addcB 121 73 111 120) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr9 43 (by omega)]; exact ho0_43aaaaaaaa
  have ho7_115aa : srun k t9 (addcB 121 73 111 120) 115 = Mont2.wadd ((Mont2.hlW (s 17) (s 19)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).2) := by
    rw [fr9 115 (by omega)]; exact ho7_115a
  have ho8_117a : srun k t9 (addcB 121 73 111 120) 117 = (Mont2.addcW ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1) ((Mont2.hlW (s 16) (s 19)).1) 0).1 := by
    rw [fr9 117 (by omega)]; exact ho8_117
  have ho9_122 : srun k t9 (addcB 121 73 111 120) 122 = (Mont2.addcW (Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2)) ((Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).1) ((Mont2.addcW ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1) ((Mont2.hlW (s 16) (s 19)).1) 0).2)).1 := by
    rw [lf17 k t9, ho3_73aaaaa, ho6_111aa, ho8_120]
  have ho9_125 : srun k t9 (addcB 121 73 111 120) 125 = (Mont2.addcW (Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2)) ((Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).1) ((Mont2.addcW ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1) ((Mont2.hlW (s 16) (s 19)).1) 0).2)).2 := by
    rw [lf18 k t9, ho3_73aaaaa, ho6_111aa, ho8_120]
  clear fr9 ho0_43aaaaaaaa ho3_73aaaaa ho6_111aa ho7_115a ho8_117 ho8_120
  generalize hg9 : srun k t9 (addcB 121 73 111 120) = t10 at ho0_43aaaaaaaaa ho7_115aa ho8_117a ho9_122 ho9_125 ⊢
  clear hg9
  have fr10 : ∀ r, r < 126 → srun k t10 ([ .binop 126 .add (.reg 115) (.reg 125) ]) r = t10 r :=
    fun r hr => srun_below k 126 ([ .binop 126 .add (.reg 115) (.reg 125) ]) (by decide +kernel) t10 r hr
  have ho0_43aaaaaaaaaa : srun k t10 ([ .binop 126 .add (.reg 115) (.reg 125) ]) 43 = (Mont2.hlW (s 16) (s 18)).1 := by
    rw [fr10 43 (by omega)]; exact ho0_43aaaaaaaaa
  have ho8_117aa : srun k t10 ([ .binop 126 .add (.reg 115) (.reg 125) ]) 117 = (Mont2.addcW ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1) ((Mont2.hlW (s 16) (s 19)).1) 0).1 := by
    rw [fr10 117 (by omega)]; exact ho8_117a
  have ho9_122a : srun k t10 ([ .binop 126 .add (.reg 115) (.reg 125) ]) 122 = (Mont2.addcW (Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2)) ((Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).1) ((Mont2.addcW ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1) ((Mont2.hlW (s 16) (s 19)).1) 0).2)).1 := by
    rw [fr10 122 (by omega)]; exact ho9_122
  have ho10_126 : srun k t10 ([ .binop 126 .add (.reg 115) (.reg 125) ]) 126 = Mont2.wadd (Mont2.wadd ((Mont2.hlW (s 17) (s 19)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).2)) ((Mont2.addcW (Mont2.wadd ((Mont2.hlW (s 17) (s 18)).2) ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).2)) ((Mont2.addcW ((Mont2.hlW (s 16) (s 19)).2) ((Mont2.hlW (s 17) (s 19)).1) 0).1) ((Mont2.addcW ((Mont2.addcW ((Mont2.hlW (s 16) (s 18)).2) ((Mont2.hlW (s 17) (s 18)).1) 0).1) ((Mont2.hlW (s 16) (s 19)).1) 0).2)).2) := by
    rw [lf19 k t10, ho7_115aa, ho9_125]
  clear fr10 ho0_43aaaaaaaaa ho7_115aa ho8_117a ho9_122 ho9_125
  generalize hg10 : srun k t10 ([ .binop 126 .add (.reg 115) (.reg 125) ]) = t11 at ho0_43aaaaaaaaaa ho8_117aa ho9_122a ho10_126 ⊢
  clear hg10
  exact ⟨ho0_43aaaaaaaaaa, ho8_117aa, ho9_122a, ho10_126⟩

theorem redcB127_spec (k : Nat) (s : RegState) :
    srun k s (redcB 127 2 3 4 43 117 122 126) 176 = (Mont2.redcStep2 (s 2) (s 3) (s 4) (s 43) (s 117) (s 122) (s 126)).1 ∧
      srun k s (redcB 127 2 3 4 43 117 122 126) 181 = (Mont2.redcStep2 (s 2) (s 3) (s 4) (s 43) (s 117) (s 122) (s 126)).2.1 ∧
      srun k s (redcB 127 2 3 4 43 117 122 126) 186 = (Mont2.redcStep2 (s 2) (s 3) (s 4) (s 43) (s 117) (s 122) (s 126)).2.2.1 ∧
      srun k s (redcB 127 2 3 4 43 117 122 126) 189 = (Mont2.redcStep2 (s 2) (s 3) (s 4) (s 43) (s 117) (s 122) (s 126)).2.2.2 := by
  have hsplit : redcB 127 2 3 4 43 117 122 126 =
      [ .binop 127 .mul (.reg 43) (.reg 4) ]
        ++ hlB 128 127 2
        ++ hlB 146 127 3
        ++ addcB0 164 145 157
        ++ [ .binop 169 .add (.reg 163) (.reg 168) ]
        ++ addcB0 170 43 139
        ++ addcB 175 117 165 174
        ++ addcB 180 122 169 179
        ++ addcBz 185 126 184 := rfl
  rw [hsplit]
  simp only [srun_append]
  have fr0 : ∀ r, r < 127 → srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) r = s r :=
    fun r hr => srun_below k 127 ([ .binop 127 .mul (.reg 43) (.reg 4) ]) (by decide +kernel) s r hr
  have hc0_2 : srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) 2 = s 2 :=
    fr0 2 (by omega)
  have hc0_3 : srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) 3 = s 3 :=
    fr0 3 (by omega)
  have hc0_43 : srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) 43 = s 43 :=
    fr0 43 (by omega)
  have hc0_117 : srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) 117 = s 117 :=
    fr0 117 (by omega)
  have hc0_122 : srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) 122 = s 122 :=
    fr0 122 (by omega)
  have hc0_126 : srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) 126 = s 126 :=
    fr0 126 (by omega)
  have ho0_127 : srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) 127 = Mont2.wmul (s 43) (s 4) := by
    rw [lf20 k s]
  clear fr0
  generalize hg0 : srun k s ([ .binop 127 .mul (.reg 43) (.reg 4) ]) = t1 at hc0_2 hc0_3 hc0_43 hc0_117 hc0_122 hc0_126 ho0_127 ⊢
  clear hg0
  have fr1 : ∀ r, r < 128 → srun k t1 (hlB 128 127 2) r = t1 r :=
    fun r hr => srun_below k 128 (hlB 128 127 2) (by decide +kernel) t1 r hr
  have hc0_3a : srun k t1 (hlB 128 127 2) 3 = s 3 := by
    rw [fr1 3 (by omega)]; exact hc0_3
  have hc0_43a : srun k t1 (hlB 128 127 2) 43 = s 43 := by
    rw [fr1 43 (by omega)]; exact hc0_43
  have hc0_117a : srun k t1 (hlB 128 127 2) 117 = s 117 := by
    rw [fr1 117 (by omega)]; exact hc0_117
  have hc0_122a : srun k t1 (hlB 128 127 2) 122 = s 122 := by
    rw [fr1 122 (by omega)]; exact hc0_122
  have hc0_126a : srun k t1 (hlB 128 127 2) 126 = s 126 := by
    rw [fr1 126 (by omega)]; exact hc0_126
  have ho0_127a : srun k t1 (hlB 128 127 2) 127 = Mont2.wmul (s 43) (s 4) := by
    rw [fr1 127 (by omega)]; exact ho0_127
  have ho1_139 : srun k t1 (hlB 128 127 2) 139 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1 := by
    rw [lf21 k t1, hc0_2, ho0_127]
  have ho1_145 : srun k t1 (hlB 128 127 2) 145 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2 := by
    rw [lf22 k t1, hc0_2, ho0_127]
  clear fr1 hc0_2 hc0_3 hc0_43 hc0_117 hc0_122 hc0_126 ho0_127
  generalize hg1 : srun k t1 (hlB 128 127 2) = t2 at hc0_3a hc0_43a hc0_117a hc0_122a hc0_126a ho0_127a ho1_139 ho1_145 ⊢
  clear hg1
  have fr2 : ∀ r, r < 146 → srun k t2 (hlB 146 127 3) r = t2 r :=
    fun r hr => srun_below k 146 (hlB 146 127 3) (by decide +kernel) t2 r hr
  have hc0_43aa : srun k t2 (hlB 146 127 3) 43 = s 43 := by
    rw [fr2 43 (by omega)]; exact hc0_43a
  have hc0_117aa : srun k t2 (hlB 146 127 3) 117 = s 117 := by
    rw [fr2 117 (by omega)]; exact hc0_117a
  have hc0_122aa : srun k t2 (hlB 146 127 3) 122 = s 122 := by
    rw [fr2 122 (by omega)]; exact hc0_122a
  have hc0_126aa : srun k t2 (hlB 146 127 3) 126 = s 126 := by
    rw [fr2 126 (by omega)]; exact hc0_126a
  have ho1_139a : srun k t2 (hlB 146 127 3) 139 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1 := by
    rw [fr2 139 (by omega)]; exact ho1_139
  have ho1_145a : srun k t2 (hlB 146 127 3) 145 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2 := by
    rw [fr2 145 (by omega)]; exact ho1_145
  have ho2_157 : srun k t2 (hlB 146 127 3) 157 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1 := by
    rw [lf23 k t2, hc0_3a, ho0_127a]
  have ho2_163 : srun k t2 (hlB 146 127 3) 163 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2 := by
    rw [lf24 k t2, hc0_3a, ho0_127a]
  clear fr2 hc0_3a hc0_43a hc0_117a hc0_122a hc0_126a ho0_127a ho1_139 ho1_145
  generalize hg2 : srun k t2 (hlB 146 127 3) = t3 at hc0_43aa hc0_117aa hc0_122aa hc0_126aa ho1_139a ho1_145a ho2_157 ho2_163 ⊢
  clear hg2
  have fr3 : ∀ r, r < 164 → srun k t3 (addcB0 164 145 157) r = t3 r :=
    fun r hr => srun_below k 164 (addcB0 164 145 157) (by decide +kernel) t3 r hr
  have hc0_43aaa : srun k t3 (addcB0 164 145 157) 43 = s 43 := by
    rw [fr3 43 (by omega)]; exact hc0_43aa
  have hc0_117aaa : srun k t3 (addcB0 164 145 157) 117 = s 117 := by
    rw [fr3 117 (by omega)]; exact hc0_117aa
  have hc0_122aaa : srun k t3 (addcB0 164 145 157) 122 = s 122 := by
    rw [fr3 122 (by omega)]; exact hc0_122aa
  have hc0_126aaa : srun k t3 (addcB0 164 145 157) 126 = s 126 := by
    rw [fr3 126 (by omega)]; exact hc0_126aa
  have ho1_139aa : srun k t3 (addcB0 164 145 157) 139 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1 := by
    rw [fr3 139 (by omega)]; exact ho1_139a
  have ho2_163a : srun k t3 (addcB0 164 145 157) 163 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2 := by
    rw [fr3 163 (by omega)]; exact ho2_163
  have ho3_165 : srun k t3 (addcB0 164 145 157) 165 = (Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1 := by
    rw [lf25 k t3, ho1_145a, ho2_157]
  have ho3_168 : srun k t3 (addcB0 164 145 157) 168 = (Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2 := by
    rw [lf26 k t3, ho1_145a, ho2_157]
  clear fr3 hc0_43aa hc0_117aa hc0_122aa hc0_126aa ho1_139a ho1_145a ho2_157 ho2_163
  generalize hg3 : srun k t3 (addcB0 164 145 157) = t4 at hc0_43aaa hc0_117aaa hc0_122aaa hc0_126aaa ho1_139aa ho2_163a ho3_165 ho3_168 ⊢
  clear hg3
  have fr4 : ∀ r, r < 169 → srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) r = t4 r :=
    fun r hr => srun_below k 169 ([ .binop 169 .add (.reg 163) (.reg 168) ]) (by decide +kernel) t4 r hr
  have hc0_43aaaa : srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) 43 = s 43 := by
    rw [fr4 43 (by omega)]; exact hc0_43aaa
  have hc0_117aaaa : srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) 117 = s 117 := by
    rw [fr4 117 (by omega)]; exact hc0_117aaa
  have hc0_122aaaa : srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) 122 = s 122 := by
    rw [fr4 122 (by omega)]; exact hc0_122aaa
  have hc0_126aaaa : srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) 126 = s 126 := by
    rw [fr4 126 (by omega)]; exact hc0_126aaa
  have ho1_139aaa : srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) 139 = (Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1 := by
    rw [fr4 139 (by omega)]; exact ho1_139aa
  have ho3_165a : srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) 165 = (Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1 := by
    rw [fr4 165 (by omega)]; exact ho3_165
  have ho4_169 : srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) 169 = Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2) := by
    rw [lf27 k t4, ho2_163a, ho3_168]
  clear fr4 hc0_43aaa hc0_117aaa hc0_122aaa hc0_126aaa ho1_139aa ho2_163a ho3_165 ho3_168
  generalize hg4 : srun k t4 ([ .binop 169 .add (.reg 163) (.reg 168) ]) = t5 at hc0_43aaaa hc0_117aaaa hc0_122aaaa hc0_126aaaa ho1_139aaa ho3_165a ho4_169 ⊢
  clear hg4
  have fr5 : ∀ r, r < 170 → srun k t5 (addcB0 170 43 139) r = t5 r :=
    fun r hr => srun_below k 170 (addcB0 170 43 139) (by decide +kernel) t5 r hr
  have hc0_117aaaaa : srun k t5 (addcB0 170 43 139) 117 = s 117 := by
    rw [fr5 117 (by omega)]; exact hc0_117aaaa
  have hc0_122aaaaa : srun k t5 (addcB0 170 43 139) 122 = s 122 := by
    rw [fr5 122 (by omega)]; exact hc0_122aaaa
  have hc0_126aaaaa : srun k t5 (addcB0 170 43 139) 126 = s 126 := by
    rw [fr5 126 (by omega)]; exact hc0_126aaaa
  have ho3_165aa : srun k t5 (addcB0 170 43 139) 165 = (Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1 := by
    rw [fr5 165 (by omega)]; exact ho3_165a
  have ho4_169a : srun k t5 (addcB0 170 43 139) 169 = Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2) := by
    rw [fr5 169 (by omega)]; exact ho4_169
  have ho5_174 : srun k t5 (addcB0 170 43 139) 174 = (Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2 := by
    rw [lf28 k t5, hc0_43aaaa, ho1_139aaa]
  clear fr5 hc0_43aaaa hc0_117aaaa hc0_122aaaa hc0_126aaaa ho1_139aaa ho3_165a ho4_169
  generalize hg5 : srun k t5 (addcB0 170 43 139) = t6 at hc0_117aaaaa hc0_122aaaaa hc0_126aaaaa ho3_165aa ho4_169a ho5_174 ⊢
  clear hg5
  have fr6 : ∀ r, r < 175 → srun k t6 (addcB 175 117 165 174) r = t6 r :=
    fun r hr => srun_below k 175 (addcB 175 117 165 174) (by decide +kernel) t6 r hr
  have hc0_122aaaaaa : srun k t6 (addcB 175 117 165 174) 122 = s 122 := by
    rw [fr6 122 (by omega)]; exact hc0_122aaaaa
  have hc0_126aaaaaa : srun k t6 (addcB 175 117 165 174) 126 = s 126 := by
    rw [fr6 126 (by omega)]; exact hc0_126aaaaa
  have ho4_169aa : srun k t6 (addcB 175 117 165 174) 169 = Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2) := by
    rw [fr6 169 (by omega)]; exact ho4_169a
  have ho6_176 : srun k t6 (addcB 175 117 165 174) 176 = (Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).1 := by
    rw [lf29 k t6, hc0_117aaaaa, ho3_165aa, ho5_174]
  have ho6_179 : srun k t6 (addcB 175 117 165 174) 179 = (Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).2 := by
    rw [lf30 k t6, hc0_117aaaaa, ho3_165aa, ho5_174]
  clear fr6 hc0_117aaaaa hc0_122aaaaa hc0_126aaaaa ho3_165aa ho4_169a ho5_174
  generalize hg6 : srun k t6 (addcB 175 117 165 174) = t7 at hc0_122aaaaaa hc0_126aaaaaa ho4_169aa ho6_176 ho6_179 ⊢
  clear hg6
  have fr7 : ∀ r, r < 180 → srun k t7 (addcB 180 122 169 179) r = t7 r :=
    fun r hr => srun_below k 180 (addcB 180 122 169 179) (by decide +kernel) t7 r hr
  have hc0_126aaaaaaa : srun k t7 (addcB 180 122 169 179) 126 = s 126 := by
    rw [fr7 126 (by omega)]; exact hc0_126aaaaaa
  have ho6_176a : srun k t7 (addcB 180 122 169 179) 176 = (Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).1 := by
    rw [fr7 176 (by omega)]; exact ho6_176
  have ho7_181 : srun k t7 (addcB 180 122 169 179) 181 = (Mont2.addcW (s 122) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).2)).1 := by
    rw [lf31 k t7, hc0_122aaaaaa, ho4_169aa, ho6_179]
  have ho7_184 : srun k t7 (addcB 180 122 169 179) 184 = (Mont2.addcW (s 122) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).2)).2 := by
    rw [lf32 k t7, hc0_122aaaaaa, ho4_169aa, ho6_179]
  clear fr7 hc0_122aaaaaa hc0_126aaaaaa ho4_169aa ho6_176 ho6_179
  generalize hg7 : srun k t7 (addcB 180 122 169 179) = t8 at hc0_126aaaaaaa ho6_176a ho7_181 ho7_184 ⊢
  clear hg7
  have fr8 : ∀ r, r < 185 → srun k t8 (addcBz 185 126 184) r = t8 r :=
    fun r hr => srun_below k 185 (addcBz 185 126 184) (by decide +kernel) t8 r hr
  have ho6_176aa : srun k t8 (addcBz 185 126 184) 176 = (Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).1 := by
    rw [fr8 176 (by omega)]; exact ho6_176a
  have ho7_181a : srun k t8 (addcBz 185 126 184) 181 = (Mont2.addcW (s 122) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).2)).1 := by
    rw [fr8 181 (by omega)]; exact ho7_181
  have ho8_186 : srun k t8 (addcBz 185 126 184) 186 = (Mont2.addcW (s 126) 0 ((Mont2.addcW (s 122) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).2)).2)).1 := by
    rw [lf33 k t8, hc0_126aaaaaaa, ho7_184]
  have ho8_189 : srun k t8 (addcBz 185 126 184) 189 = (Mont2.addcW (s 126) 0 ((Mont2.addcW (s 122) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 117) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 43) ((Mont2.hlW (Mont2.wmul (s 43) (s 4)) (s 2)).1) 0).2)).2)).2)).2 := by
    rw [lf34 k t8, hc0_126aaaaaaa, ho7_184]
  clear fr8 hc0_126aaaaaaa ho6_176a ho7_181 ho7_184
  generalize hg8 : srun k t8 (addcBz 185 126 184) = t9 at ho6_176aa ho7_181a ho8_186 ho8_189 ⊢
  clear hg8
  exact ⟨ho6_176aa, ho7_181a, ho8_186, ho8_189⟩

theorem redcB190_spec (k : Nat) (s : RegState) :
    srun k s (redcB 190 2 3 4 176 181 186 189) 239 = (Mont2.redcStep2 (s 2) (s 3) (s 4) (s 176) (s 181) (s 186) (s 189)).1 ∧
      srun k s (redcB 190 2 3 4 176 181 186 189) 244 = (Mont2.redcStep2 (s 2) (s 3) (s 4) (s 176) (s 181) (s 186) (s 189)).2.1 ∧
      srun k s (redcB 190 2 3 4 176 181 186 189) 249 = (Mont2.redcStep2 (s 2) (s 3) (s 4) (s 176) (s 181) (s 186) (s 189)).2.2.1 ∧
      srun k s (redcB 190 2 3 4 176 181 186 189) 252 = (Mont2.redcStep2 (s 2) (s 3) (s 4) (s 176) (s 181) (s 186) (s 189)).2.2.2 := by
  have hsplit : redcB 190 2 3 4 176 181 186 189 =
      [ .binop 190 .mul (.reg 176) (.reg 4) ]
        ++ hlB 191 190 2
        ++ hlB 209 190 3
        ++ addcB0 227 208 220
        ++ [ .binop 232 .add (.reg 226) (.reg 231) ]
        ++ addcB0 233 176 202
        ++ addcB 238 181 228 237
        ++ addcB 243 186 232 242
        ++ addcBz 248 189 247 := rfl
  rw [hsplit]
  simp only [srun_append]
  have fr0 : ∀ r, r < 190 → srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) r = s r :=
    fun r hr => srun_below k 190 ([ .binop 190 .mul (.reg 176) (.reg 4) ]) (by decide +kernel) s r hr
  have hc0_2 : srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) 2 = s 2 :=
    fr0 2 (by omega)
  have hc0_3 : srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) 3 = s 3 :=
    fr0 3 (by omega)
  have hc0_176 : srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) 176 = s 176 :=
    fr0 176 (by omega)
  have hc0_181 : srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) 181 = s 181 :=
    fr0 181 (by omega)
  have hc0_186 : srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) 186 = s 186 :=
    fr0 186 (by omega)
  have hc0_189 : srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) 189 = s 189 :=
    fr0 189 (by omega)
  have ho0_190 : srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) 190 = Mont2.wmul (s 176) (s 4) := by
    rw [lf35 k s]
  clear fr0
  generalize hg0 : srun k s ([ .binop 190 .mul (.reg 176) (.reg 4) ]) = t1 at hc0_2 hc0_3 hc0_176 hc0_181 hc0_186 hc0_189 ho0_190 ⊢
  clear hg0
  have fr1 : ∀ r, r < 191 → srun k t1 (hlB 191 190 2) r = t1 r :=
    fun r hr => srun_below k 191 (hlB 191 190 2) (by decide +kernel) t1 r hr
  have hc0_3a : srun k t1 (hlB 191 190 2) 3 = s 3 := by
    rw [fr1 3 (by omega)]; exact hc0_3
  have hc0_176a : srun k t1 (hlB 191 190 2) 176 = s 176 := by
    rw [fr1 176 (by omega)]; exact hc0_176
  have hc0_181a : srun k t1 (hlB 191 190 2) 181 = s 181 := by
    rw [fr1 181 (by omega)]; exact hc0_181
  have hc0_186a : srun k t1 (hlB 191 190 2) 186 = s 186 := by
    rw [fr1 186 (by omega)]; exact hc0_186
  have hc0_189a : srun k t1 (hlB 191 190 2) 189 = s 189 := by
    rw [fr1 189 (by omega)]; exact hc0_189
  have ho0_190a : srun k t1 (hlB 191 190 2) 190 = Mont2.wmul (s 176) (s 4) := by
    rw [fr1 190 (by omega)]; exact ho0_190
  have ho1_202 : srun k t1 (hlB 191 190 2) 202 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1 := by
    rw [lf36 k t1, hc0_2, ho0_190]
  have ho1_208 : srun k t1 (hlB 191 190 2) 208 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2 := by
    rw [lf37 k t1, hc0_2, ho0_190]
  clear fr1 hc0_2 hc0_3 hc0_176 hc0_181 hc0_186 hc0_189 ho0_190
  generalize hg1 : srun k t1 (hlB 191 190 2) = t2 at hc0_3a hc0_176a hc0_181a hc0_186a hc0_189a ho0_190a ho1_202 ho1_208 ⊢
  clear hg1
  have fr2 : ∀ r, r < 209 → srun k t2 (hlB 209 190 3) r = t2 r :=
    fun r hr => srun_below k 209 (hlB 209 190 3) (by decide +kernel) t2 r hr
  have hc0_176aa : srun k t2 (hlB 209 190 3) 176 = s 176 := by
    rw [fr2 176 (by omega)]; exact hc0_176a
  have hc0_181aa : srun k t2 (hlB 209 190 3) 181 = s 181 := by
    rw [fr2 181 (by omega)]; exact hc0_181a
  have hc0_186aa : srun k t2 (hlB 209 190 3) 186 = s 186 := by
    rw [fr2 186 (by omega)]; exact hc0_186a
  have hc0_189aa : srun k t2 (hlB 209 190 3) 189 = s 189 := by
    rw [fr2 189 (by omega)]; exact hc0_189a
  have ho1_202a : srun k t2 (hlB 209 190 3) 202 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1 := by
    rw [fr2 202 (by omega)]; exact ho1_202
  have ho1_208a : srun k t2 (hlB 209 190 3) 208 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2 := by
    rw [fr2 208 (by omega)]; exact ho1_208
  have ho2_220 : srun k t2 (hlB 209 190 3) 220 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1 := by
    rw [lf38 k t2, hc0_3a, ho0_190a]
  have ho2_226 : srun k t2 (hlB 209 190 3) 226 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2 := by
    rw [lf39 k t2, hc0_3a, ho0_190a]
  clear fr2 hc0_3a hc0_176a hc0_181a hc0_186a hc0_189a ho0_190a ho1_202 ho1_208
  generalize hg2 : srun k t2 (hlB 209 190 3) = t3 at hc0_176aa hc0_181aa hc0_186aa hc0_189aa ho1_202a ho1_208a ho2_220 ho2_226 ⊢
  clear hg2
  have fr3 : ∀ r, r < 227 → srun k t3 (addcB0 227 208 220) r = t3 r :=
    fun r hr => srun_below k 227 (addcB0 227 208 220) (by decide +kernel) t3 r hr
  have hc0_176aaa : srun k t3 (addcB0 227 208 220) 176 = s 176 := by
    rw [fr3 176 (by omega)]; exact hc0_176aa
  have hc0_181aaa : srun k t3 (addcB0 227 208 220) 181 = s 181 := by
    rw [fr3 181 (by omega)]; exact hc0_181aa
  have hc0_186aaa : srun k t3 (addcB0 227 208 220) 186 = s 186 := by
    rw [fr3 186 (by omega)]; exact hc0_186aa
  have hc0_189aaa : srun k t3 (addcB0 227 208 220) 189 = s 189 := by
    rw [fr3 189 (by omega)]; exact hc0_189aa
  have ho1_202aa : srun k t3 (addcB0 227 208 220) 202 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1 := by
    rw [fr3 202 (by omega)]; exact ho1_202a
  have ho2_226a : srun k t3 (addcB0 227 208 220) 226 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2 := by
    rw [fr3 226 (by omega)]; exact ho2_226
  have ho3_228 : srun k t3 (addcB0 227 208 220) 228 = (Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1 := by
    rw [lf40 k t3, ho1_208a, ho2_220]
  have ho3_231 : srun k t3 (addcB0 227 208 220) 231 = (Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2 := by
    rw [lf41 k t3, ho1_208a, ho2_220]
  clear fr3 hc0_176aa hc0_181aa hc0_186aa hc0_189aa ho1_202a ho1_208a ho2_220 ho2_226
  generalize hg3 : srun k t3 (addcB0 227 208 220) = t4 at hc0_176aaa hc0_181aaa hc0_186aaa hc0_189aaa ho1_202aa ho2_226a ho3_228 ho3_231 ⊢
  clear hg3
  have fr4 : ∀ r, r < 232 → srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) r = t4 r :=
    fun r hr => srun_below k 232 ([ .binop 232 .add (.reg 226) (.reg 231) ]) (by decide +kernel) t4 r hr
  have hc0_176aaaa : srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) 176 = s 176 := by
    rw [fr4 176 (by omega)]; exact hc0_176aaa
  have hc0_181aaaa : srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) 181 = s 181 := by
    rw [fr4 181 (by omega)]; exact hc0_181aaa
  have hc0_186aaaa : srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) 186 = s 186 := by
    rw [fr4 186 (by omega)]; exact hc0_186aaa
  have hc0_189aaaa : srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) 189 = s 189 := by
    rw [fr4 189 (by omega)]; exact hc0_189aaa
  have ho1_202aaa : srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) 202 = (Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1 := by
    rw [fr4 202 (by omega)]; exact ho1_202aa
  have ho3_228a : srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) 228 = (Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1 := by
    rw [fr4 228 (by omega)]; exact ho3_228
  have ho4_232 : srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) 232 = Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2) := by
    rw [lf42 k t4, ho2_226a, ho3_231]
  clear fr4 hc0_176aaa hc0_181aaa hc0_186aaa hc0_189aaa ho1_202aa ho2_226a ho3_228 ho3_231
  generalize hg4 : srun k t4 ([ .binop 232 .add (.reg 226) (.reg 231) ]) = t5 at hc0_176aaaa hc0_181aaaa hc0_186aaaa hc0_189aaaa ho1_202aaa ho3_228a ho4_232 ⊢
  clear hg4
  have fr5 : ∀ r, r < 233 → srun k t5 (addcB0 233 176 202) r = t5 r :=
    fun r hr => srun_below k 233 (addcB0 233 176 202) (by decide +kernel) t5 r hr
  have hc0_181aaaaa : srun k t5 (addcB0 233 176 202) 181 = s 181 := by
    rw [fr5 181 (by omega)]; exact hc0_181aaaa
  have hc0_186aaaaa : srun k t5 (addcB0 233 176 202) 186 = s 186 := by
    rw [fr5 186 (by omega)]; exact hc0_186aaaa
  have hc0_189aaaaa : srun k t5 (addcB0 233 176 202) 189 = s 189 := by
    rw [fr5 189 (by omega)]; exact hc0_189aaaa
  have ho3_228aa : srun k t5 (addcB0 233 176 202) 228 = (Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1 := by
    rw [fr5 228 (by omega)]; exact ho3_228a
  have ho4_232a : srun k t5 (addcB0 233 176 202) 232 = Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2) := by
    rw [fr5 232 (by omega)]; exact ho4_232
  have ho5_237 : srun k t5 (addcB0 233 176 202) 237 = (Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2 := by
    rw [lf43 k t5, hc0_176aaaa, ho1_202aaa]
  clear fr5 hc0_176aaaa hc0_181aaaa hc0_186aaaa hc0_189aaaa ho1_202aaa ho3_228a ho4_232
  generalize hg5 : srun k t5 (addcB0 233 176 202) = t6 at hc0_181aaaaa hc0_186aaaaa hc0_189aaaaa ho3_228aa ho4_232a ho5_237 ⊢
  clear hg5
  have fr6 : ∀ r, r < 238 → srun k t6 (addcB 238 181 228 237) r = t6 r :=
    fun r hr => srun_below k 238 (addcB 238 181 228 237) (by decide +kernel) t6 r hr
  have hc0_186aaaaaa : srun k t6 (addcB 238 181 228 237) 186 = s 186 := by
    rw [fr6 186 (by omega)]; exact hc0_186aaaaa
  have hc0_189aaaaaa : srun k t6 (addcB 238 181 228 237) 189 = s 189 := by
    rw [fr6 189 (by omega)]; exact hc0_189aaaaa
  have ho4_232aa : srun k t6 (addcB 238 181 228 237) 232 = Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2) := by
    rw [fr6 232 (by omega)]; exact ho4_232a
  have ho6_239 : srun k t6 (addcB 238 181 228 237) 239 = (Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).1 := by
    rw [lf44 k t6, hc0_181aaaaa, ho3_228aa, ho5_237]
  have ho6_242 : srun k t6 (addcB 238 181 228 237) 242 = (Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).2 := by
    rw [lf45 k t6, hc0_181aaaaa, ho3_228aa, ho5_237]
  clear fr6 hc0_181aaaaa hc0_186aaaaa hc0_189aaaaa ho3_228aa ho4_232a ho5_237
  generalize hg6 : srun k t6 (addcB 238 181 228 237) = t7 at hc0_186aaaaaa hc0_189aaaaaa ho4_232aa ho6_239 ho6_242 ⊢
  clear hg6
  have fr7 : ∀ r, r < 243 → srun k t7 (addcB 243 186 232 242) r = t7 r :=
    fun r hr => srun_below k 243 (addcB 243 186 232 242) (by decide +kernel) t7 r hr
  have hc0_189aaaaaaa : srun k t7 (addcB 243 186 232 242) 189 = s 189 := by
    rw [fr7 189 (by omega)]; exact hc0_189aaaaaa
  have ho6_239a : srun k t7 (addcB 243 186 232 242) 239 = (Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).1 := by
    rw [fr7 239 (by omega)]; exact ho6_239
  have ho7_244 : srun k t7 (addcB 243 186 232 242) 244 = (Mont2.addcW (s 186) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).2)).1 := by
    rw [lf46 k t7, hc0_186aaaaaa, ho4_232aa, ho6_242]
  have ho7_247 : srun k t7 (addcB 243 186 232 242) 247 = (Mont2.addcW (s 186) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).2)).2 := by
    rw [lf47 k t7, hc0_186aaaaaa, ho4_232aa, ho6_242]
  clear fr7 hc0_186aaaaaa hc0_189aaaaaa ho4_232aa ho6_239 ho6_242
  generalize hg7 : srun k t7 (addcB 243 186 232 242) = t8 at hc0_189aaaaaaa ho6_239a ho7_244 ho7_247 ⊢
  clear hg7
  have fr8 : ∀ r, r < 248 → srun k t8 (addcBz 248 189 247) r = t8 r :=
    fun r hr => srun_below k 248 (addcBz 248 189 247) (by decide +kernel) t8 r hr
  have ho6_239aa : srun k t8 (addcBz 248 189 247) 239 = (Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).1 := by
    rw [fr8 239 (by omega)]; exact ho6_239a
  have ho7_244a : srun k t8 (addcBz 248 189 247) 244 = (Mont2.addcW (s 186) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).2)).1 := by
    rw [fr8 244 (by omega)]; exact ho7_244
  have ho8_249 : srun k t8 (addcBz 248 189 247) 249 = (Mont2.addcW (s 189) 0 ((Mont2.addcW (s 186) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).2)).2)).1 := by
    rw [lf48 k t8, hc0_189aaaaaaa, ho7_247]
  have ho8_252 : srun k t8 (addcBz 248 189 247) 252 = (Mont2.addcW (s 189) 0 ((Mont2.addcW (s 186) (Mont2.wadd ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).2) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).2)) ((Mont2.addcW (s 181) ((Mont2.addcW ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).2) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 3)).1) 0).1) ((Mont2.addcW (s 176) ((Mont2.hlW (Mont2.wmul (s 176) (s 4)) (s 2)).1) 0).2)).2)).2)).2 := by
    rw [lf49 k t8, hc0_189aaaaaaa, ho7_247]
  clear fr8 hc0_189aaaaaaa ho6_239a ho7_244 ho7_247
  generalize hg8 : srun k t8 (addcBz 248 189 247) = t9 at ho6_239aa ho7_244a ho8_249 ho8_252 ⊢
  clear hg8
  exact ⟨ho6_239aa, ho7_244a, ho8_249, ho8_252⟩

theorem csB_spec (k : Nat) (s : RegState) :
    srun k s (csB 253 2 3 239 244) 267 = (Mont2.condSub2 (s 2) (s 3) (s 239) (s 244)).1 ∧
      srun k s (csB 253 2 3 239 244) 271 = (Mont2.condSub2 (s 2) (s 3) (s 239) (s 244)).2 := by
  have hsplit : csB 253 2 3 239 244 =
      sbbB0 253 239 2
        ++ sbbB 258 244 3 257
        ++ [ .binop 263 .sub (.lit 1) (.reg 262) ]
        ++ selB 264 263 254 239
        ++ selB 268 263 259 244 := rfl
  rw [hsplit]
  simp only [srun_append]
  have fr0 : ∀ r, r < 253 → srun k s (sbbB0 253 239 2) r = s r :=
    fun r hr => srun_below k 253 (sbbB0 253 239 2) (by decide +kernel) s r hr
  have hc0_3 : srun k s (sbbB0 253 239 2) 3 = s 3 :=
    fr0 3 (by omega)
  have hc0_239 : srun k s (sbbB0 253 239 2) 239 = s 239 :=
    fr0 239 (by omega)
  have hc0_244 : srun k s (sbbB0 253 239 2) 244 = s 244 :=
    fr0 244 (by omega)
  have ho0_254 : srun k s (sbbB0 253 239 2) 254 = (Mont2.sbbcW (s 239) (s 2) 0).1 := by
    rw [lf50 k s]
  have ho0_257 : srun k s (sbbB0 253 239 2) 257 = (Mont2.sbbcW (s 239) (s 2) 0).2 := by
    rw [lf51 k s]
  clear fr0
  generalize hg0 : srun k s (sbbB0 253 239 2) = t1 at hc0_3 hc0_239 hc0_244 ho0_254 ho0_257 ⊢
  clear hg0
  have fr1 : ∀ r, r < 258 → srun k t1 (sbbB 258 244 3 257) r = t1 r :=
    fun r hr => srun_below k 258 (sbbB 258 244 3 257) (by decide +kernel) t1 r hr
  have hc0_239a : srun k t1 (sbbB 258 244 3 257) 239 = s 239 := by
    rw [fr1 239 (by omega)]; exact hc0_239
  have hc0_244a : srun k t1 (sbbB 258 244 3 257) 244 = s 244 := by
    rw [fr1 244 (by omega)]; exact hc0_244
  have ho0_254a : srun k t1 (sbbB 258 244 3 257) 254 = (Mont2.sbbcW (s 239) (s 2) 0).1 := by
    rw [fr1 254 (by omega)]; exact ho0_254
  have ho1_259 : srun k t1 (sbbB 258 244 3 257) 259 = (Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).1 := by
    rw [lf52 k t1, hc0_3, hc0_244, ho0_257]
  have ho1_262 : srun k t1 (sbbB 258 244 3 257) 262 = (Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).2 := by
    rw [lf53 k t1, hc0_3, hc0_244, ho0_257]
  clear fr1 hc0_3 hc0_239 hc0_244 ho0_254 ho0_257
  generalize hg1 : srun k t1 (sbbB 258 244 3 257) = t2 at hc0_239a hc0_244a ho0_254a ho1_259 ho1_262 ⊢
  clear hg1
  have fr2 : ∀ r, r < 263 → srun k t2 ([ .binop 263 .sub (.lit 1) (.reg 262) ]) r = t2 r :=
    fun r hr => srun_below k 263 ([ .binop 263 .sub (.lit 1) (.reg 262) ]) (by decide +kernel) t2 r hr
  have hc0_239aa : srun k t2 ([ .binop 263 .sub (.lit 1) (.reg 262) ]) 239 = s 239 := by
    rw [fr2 239 (by omega)]; exact hc0_239a
  have hc0_244aa : srun k t2 ([ .binop 263 .sub (.lit 1) (.reg 262) ]) 244 = s 244 := by
    rw [fr2 244 (by omega)]; exact hc0_244a
  have ho0_254aa : srun k t2 ([ .binop 263 .sub (.lit 1) (.reg 262) ]) 254 = (Mont2.sbbcW (s 239) (s 2) 0).1 := by
    rw [fr2 254 (by omega)]; exact ho0_254a
  have ho1_259a : srun k t2 ([ .binop 263 .sub (.lit 1) (.reg 262) ]) 259 = (Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).1 := by
    rw [fr2 259 (by omega)]; exact ho1_259
  have ho2_263 : srun k t2 ([ .binop 263 .sub (.lit 1) (.reg 262) ]) 263 = Mont2.wsub 1 ((Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).2) := by
    rw [lf54 k t2, ho1_262]
  clear fr2 hc0_239a hc0_244a ho0_254a ho1_259 ho1_262
  generalize hg2 : srun k t2 ([ .binop 263 .sub (.lit 1) (.reg 262) ]) = t3 at hc0_239aa hc0_244aa ho0_254aa ho1_259a ho2_263 ⊢
  clear hg2
  have fr3 : ∀ r, r < 264 → srun k t3 (selB 264 263 254 239) r = t3 r :=
    fun r hr => srun_below k 264 (selB 264 263 254 239) (by decide +kernel) t3 r hr
  have hc0_244aaa : srun k t3 (selB 264 263 254 239) 244 = s 244 := by
    rw [fr3 244 (by omega)]; exact hc0_244aa
  have ho1_259aa : srun k t3 (selB 264 263 254 239) 259 = (Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).1 := by
    rw [fr3 259 (by omega)]; exact ho1_259a
  have ho2_263a : srun k t3 (selB 264 263 254 239) 263 = Mont2.wsub 1 ((Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).2) := by
    rw [fr3 263 (by omega)]; exact ho2_263
  have ho3_267 : srun k t3 (selB 264 263 254 239) 267 = Mont2.wsel (Mont2.wsub 1 ((Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).2)) ((Mont2.sbbcW (s 239) (s 2) 0).1) (s 239) := by
    rw [lf55 k t3, hc0_239aa, ho0_254aa, ho2_263]
  clear fr3 hc0_239aa hc0_244aa ho0_254aa ho1_259a ho2_263
  generalize hg3 : srun k t3 (selB 264 263 254 239) = t4 at hc0_244aaa ho1_259aa ho2_263a ho3_267 ⊢
  clear hg3
  have fr4 : ∀ r, r < 268 → srun k t4 (selB 268 263 259 244) r = t4 r :=
    fun r hr => srun_below k 268 (selB 268 263 259 244) (by decide +kernel) t4 r hr
  have ho3_267a : srun k t4 (selB 268 263 259 244) 267 = Mont2.wsel (Mont2.wsub 1 ((Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).2)) ((Mont2.sbbcW (s 239) (s 2) 0).1) (s 239) := by
    rw [fr4 267 (by omega)]; exact ho3_267
  have ho4_271 : srun k t4 (selB 268 263 259 244) 271 = Mont2.wsel (Mont2.wsub 1 ((Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).2)) ((Mont2.sbbcW (s 244) (s 3) ((Mont2.sbbcW (s 239) (s 2) 0).2)).1) (s 244) := by
    rw [lf56 k t4, hc0_244aaa, ho1_259aa, ho2_263a]
  clear fr4 hc0_244aaa ho1_259aa ho2_263a ho3_267
  generalize hg4 : srun k t4 (selB 268 263 259 244) = t5 at ho3_267a ho4_271 ⊢
  clear hg4
  exact ⟨ho3_267a, ho4_271⟩

theorem mmBlock_spec (k : Nat) (s : RegState) :
    srun k s (mmBlock) 267 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 16) (s 17) (s 18) (s 19)).1 ∧
      srun k s (mmBlock) 271 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 16) (s 17) (s 18) (s 19)).2 := by
  have hsplit : mmBlock =
      mul2B 32 16 17 18 19
        ++ redcB 127 2 3 4 43 117 122 126
        ++ redcB 190 2 3 4 176 181 186 189
        ++ csB 253 2 3 239 244 := rfl
  rw [hsplit]
  simp only [srun_append]
  have fr0 : ∀ r, r < 32 → srun k s (mul2B 32 16 17 18 19) r = s r :=
    fun r hr => srun_below k 32 (mul2B 32 16 17 18 19) (by decide +kernel) s r hr
  have hc0_2 : srun k s (mul2B 32 16 17 18 19) 2 = s 2 :=
    fr0 2 (by omega)
  have hc0_3 : srun k s (mul2B 32 16 17 18 19) 3 = s 3 :=
    fr0 3 (by omega)
  have hc0_4 : srun k s (mul2B 32 16 17 18 19) 4 = s 4 :=
    fr0 4 (by omega)
  have ho0_43 : srun k s (mul2B 32 16 17 18 19) 43 = (Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1 := by
    rw [(mul2B_spec k s).1]
  have ho0_117 : srun k s (mul2B 32 16 17 18 19) 117 = (Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1 := by
    rw [(mul2B_spec k s).2.1]
  have ho0_122 : srun k s (mul2B 32 16 17 18 19) 122 = (Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1 := by
    rw [(mul2B_spec k s).2.2.1]
  have ho0_126 : srun k s (mul2B 32 16 17 18 19) 126 = (Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2 := by
    rw [(mul2B_spec k s).2.2.2]
  clear fr0
  generalize hg0 : srun k s (mul2B 32 16 17 18 19) = t1 at hc0_2 hc0_3 hc0_4 ho0_43 ho0_117 ho0_122 ho0_126 ⊢
  clear hg0
  have fr1 : ∀ r, r < 127 → srun k t1 (redcB 127 2 3 4 43 117 122 126) r = t1 r :=
    fun r hr => srun_below k 127 (redcB 127 2 3 4 43 117 122 126) (by decide +kernel) t1 r hr
  have hc0_2a : srun k t1 (redcB 127 2 3 4 43 117 122 126) 2 = s 2 := by
    rw [fr1 2 (by omega)]; exact hc0_2
  have hc0_3a : srun k t1 (redcB 127 2 3 4 43 117 122 126) 3 = s 3 := by
    rw [fr1 3 (by omega)]; exact hc0_3
  have hc0_4a : srun k t1 (redcB 127 2 3 4 43 117 122 126) 4 = s 4 := by
    rw [fr1 4 (by omega)]; exact hc0_4
  have ho1_176 : srun k t1 (redcB 127 2 3 4 43 117 122 126) 176 = (Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).1 := by
    rw [(redcB127_spec k t1).1, hc0_2, hc0_3, hc0_4, ho0_43, ho0_117, ho0_122, ho0_126]
  have ho1_181 : srun k t1 (redcB 127 2 3 4 43 117 122 126) 181 = (Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.1 := by
    rw [(redcB127_spec k t1).2.1, hc0_2, hc0_3, hc0_4, ho0_43, ho0_117, ho0_122, ho0_126]
  have ho1_186 : srun k t1 (redcB 127 2 3 4 43 117 122 126) 186 = (Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.1 := by
    rw [(redcB127_spec k t1).2.2.1, hc0_2, hc0_3, hc0_4, ho0_43, ho0_117, ho0_122, ho0_126]
  have ho1_189 : srun k t1 (redcB 127 2 3 4 43 117 122 126) 189 = (Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.2 := by
    rw [(redcB127_spec k t1).2.2.2, hc0_2, hc0_3, hc0_4, ho0_43, ho0_117, ho0_122, ho0_126]
  clear fr1 hc0_2 hc0_3 hc0_4 ho0_43 ho0_117 ho0_122 ho0_126
  generalize hg1 : srun k t1 (redcB 127 2 3 4 43 117 122 126) = t2 at hc0_2a hc0_3a hc0_4a ho1_176 ho1_181 ho1_186 ho1_189 ⊢
  clear hg1
  have fr2 : ∀ r, r < 190 → srun k t2 (redcB 190 2 3 4 176 181 186 189) r = t2 r :=
    fun r hr => srun_below k 190 (redcB 190 2 3 4 176 181 186 189) (by decide +kernel) t2 r hr
  have hc0_2aa : srun k t2 (redcB 190 2 3 4 176 181 186 189) 2 = s 2 := by
    rw [fr2 2 (by omega)]; exact hc0_2a
  have hc0_3aa : srun k t2 (redcB 190 2 3 4 176 181 186 189) 3 = s 3 := by
    rw [fr2 3 (by omega)]; exact hc0_3a
  have ho2_239 : srun k t2 (redcB 190 2 3 4 176 181 186 189) 239 = (Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.2)).1 := by
    rw [(redcB190_spec k t2).1, hc0_2a, hc0_3a, hc0_4a, ho1_176, ho1_181, ho1_186, ho1_189]
  have ho2_244 : srun k t2 (redcB 190 2 3 4 176 181 186 189) 244 = (Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.2)).2.1 := by
    rw [(redcB190_spec k t2).2.1, hc0_2a, hc0_3a, hc0_4a, ho1_176, ho1_181, ho1_186, ho1_189]
  clear fr2 hc0_2a hc0_3a hc0_4a ho1_176 ho1_181 ho1_186 ho1_189
  generalize hg2 : srun k t2 (redcB 190 2 3 4 176 181 186 189) = t3 at hc0_2aa hc0_3aa ho2_239 ho2_244 ⊢
  clear hg2
  have fr3 : ∀ r, r < 253 → srun k t3 (csB 253 2 3 239 244) r = t3 r :=
    fun r hr => srun_below k 253 (csB 253 2 3 239 244) (by decide +kernel) t3 r hr
  have ho3_267 : srun k t3 (csB 253 2 3 239 244) 267 = (Mont2.condSub2 (s 2) (s 3) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.2)).1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.2)).2.1)).1 := by
    rw [(csB_spec k t3).1, hc0_2aa, hc0_3aa, ho2_239, ho2_244]
  have ho3_271 : srun k t3 (csB 253 2 3 239 244) 271 = (Mont2.condSub2 (s 2) (s 3) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.2)).1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.1) ((Mont2.redcStep2 (s 2) (s 3) (s 4) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.1) ((Mont2.mul2 (s 16) (s 17) (s 18) (s 19)).2.2.2)).2.2.2)).2.1)).2 := by
    rw [(csB_spec k t3).2, hc0_2aa, hc0_3aa, ho2_239, ho2_244]
  clear fr3 hc0_2aa hc0_3aa ho2_239 ho2_244
  generalize hg3 : srun k t3 (csB 253 2 3 239 244) = t4 at ho3_267 ho3_271 ⊢
  clear hg3
  exact ⟨ho3_267, ho3_271⟩

theorem bodyTail_spec (k : Nat) (s : RegState) :
    srun k s (bodyTail) 5 = (Mont2.montMul2 (s 2) (s 3) (s 4) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2) (Mont2.wsel (s 13) (s 7) (s 9)) (Mont2.wsel (s 13) (s 8) (s 10))).1 ∧
      srun k s (bodyTail) 6 = (Mont2.montMul2 (s 2) (s 3) (s 4) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2) (Mont2.wsel (s 13) (s 7) (s 9)) (Mont2.wsel (s 13) (s 8) (s 10))).2 := by
  have hsplit : bodyTail =
      selB 23 13 7 9
        ++ selB 27 13 8 10
        ++ [ .mov 14 (.reg 26), .mov 15 (.reg 30) ]
        ++ loadA 5 6
        ++ loadB 5 6
        ++ mmBlock
        ++ storeC 5 6
        ++ loadA 5 6
        ++ loadB 14 15
        ++ mmBlock
        ++ storeC 5 6 := rfl
  rw [hsplit]
  simp only [srun_append]
  have hc0_2 : srun k s (selB 23 13 7 9) 2 = s 2 :=
    srun_untouched k 2 (selB 23 13 7 9) (by decide +kernel) s
  have hc0_3 : srun k s (selB 23 13 7 9) 3 = s 3 :=
    srun_untouched k 3 (selB 23 13 7 9) (by decide +kernel) s
  have hc0_4 : srun k s (selB 23 13 7 9) 4 = s 4 :=
    srun_untouched k 4 (selB 23 13 7 9) (by decide +kernel) s
  have hc0_5 : srun k s (selB 23 13 7 9) 5 = s 5 :=
    srun_untouched k 5 (selB 23 13 7 9) (by decide +kernel) s
  have hc0_6 : srun k s (selB 23 13 7 9) 6 = s 6 :=
    srun_untouched k 6 (selB 23 13 7 9) (by decide +kernel) s
  have hc0_8 : srun k s (selB 23 13 7 9) 8 = s 8 :=
    srun_untouched k 8 (selB 23 13 7 9) (by decide +kernel) s
  have hc0_10 : srun k s (selB 23 13 7 9) 10 = s 10 :=
    srun_untouched k 10 (selB 23 13 7 9) (by decide +kernel) s
  have hc0_13 : srun k s (selB 23 13 7 9) 13 = s 13 :=
    srun_untouched k 13 (selB 23 13 7 9) (by decide +kernel) s
  have ho0_26 : srun k s (selB 23 13 7 9) 26 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [lf57 k s]
  generalize hg0 : srun k s (selB 23 13 7 9) = t1 at hc0_2 hc0_3 hc0_4 hc0_5 hc0_6 hc0_8 hc0_10 hc0_13 ho0_26 ⊢
  clear hg0
  have hc0_2a : srun k t1 (selB 27 13 8 10) 2 = s 2 := by
    rw [srun_untouched k 2 (selB 27 13 8 10) (by decide +kernel) t1]
    exact hc0_2
  have hc0_3a : srun k t1 (selB 27 13 8 10) 3 = s 3 := by
    rw [srun_untouched k 3 (selB 27 13 8 10) (by decide +kernel) t1]
    exact hc0_3
  have hc0_4a : srun k t1 (selB 27 13 8 10) 4 = s 4 := by
    rw [srun_untouched k 4 (selB 27 13 8 10) (by decide +kernel) t1]
    exact hc0_4
  have hc0_5a : srun k t1 (selB 27 13 8 10) 5 = s 5 := by
    rw [srun_untouched k 5 (selB 27 13 8 10) (by decide +kernel) t1]
    exact hc0_5
  have hc0_6a : srun k t1 (selB 27 13 8 10) 6 = s 6 := by
    rw [srun_untouched k 6 (selB 27 13 8 10) (by decide +kernel) t1]
    exact hc0_6
  have ho0_26a : srun k t1 (selB 27 13 8 10) 26 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [srun_untouched k 26 (selB 27 13 8 10) (by decide +kernel) t1]
    exact ho0_26
  have ho1_30 : srun k t1 (selB 27 13 8 10) 30 = Mont2.wsel (s 13) (s 8) (s 10) := by
    rw [lf58 k t1, hc0_8, hc0_10, hc0_13]
  clear hc0_2 hc0_3 hc0_4 hc0_5 hc0_6 hc0_8 hc0_10 hc0_13 ho0_26
  generalize hg1 : srun k t1 (selB 27 13 8 10) = t2 at hc0_2a hc0_3a hc0_4a hc0_5a hc0_6a ho0_26a ho1_30 ⊢
  clear hg1
  have hc0_2aa : srun k t2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 2 = s 2 := by
    rw [srun_untouched k 2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) (by decide +kernel) t2]
    exact hc0_2a
  have hc0_3aa : srun k t2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 3 = s 3 := by
    rw [srun_untouched k 3 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) (by decide +kernel) t2]
    exact hc0_3a
  have hc0_4aa : srun k t2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 4 = s 4 := by
    rw [srun_untouched k 4 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) (by decide +kernel) t2]
    exact hc0_4a
  have hc0_5aa : srun k t2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 5 = s 5 := by
    rw [srun_untouched k 5 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) (by decide +kernel) t2]
    exact hc0_5a
  have hc0_6aa : srun k t2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 6 = s 6 := by
    rw [srun_untouched k 6 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) (by decide +kernel) t2]
    exact hc0_6a
  have ho2_14 : srun k t2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 14 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [lf59 k t2, ho0_26a]
  have ho2_15 : srun k t2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) 15 = Mont2.wsel (s 13) (s 8) (s 10) := by
    rw [lf60 k t2, ho1_30]
  clear hc0_2a hc0_3a hc0_4a hc0_5a hc0_6a ho0_26a ho1_30
  generalize hg2 : srun k t2 ([ .mov 14 (.reg 26), .mov 15 (.reg 30) ]) = t3 at hc0_2aa hc0_3aa hc0_4aa hc0_5aa hc0_6aa ho2_14 ho2_15 ⊢
  clear hg2
  have hc0_2aaa : srun k t3 (loadA 5 6) 2 = s 2 := by
    rw [srun_untouched k 2 (loadA 5 6) (by decide +kernel) t3]
    exact hc0_2aa
  have hc0_3aaa : srun k t3 (loadA 5 6) 3 = s 3 := by
    rw [srun_untouched k 3 (loadA 5 6) (by decide +kernel) t3]
    exact hc0_3aa
  have hc0_4aaa : srun k t3 (loadA 5 6) 4 = s 4 := by
    rw [srun_untouched k 4 (loadA 5 6) (by decide +kernel) t3]
    exact hc0_4aa
  have hc0_5aaa : srun k t3 (loadA 5 6) 5 = s 5 := by
    rw [srun_untouched k 5 (loadA 5 6) (by decide +kernel) t3]
    exact hc0_5aa
  have hc0_6aaa : srun k t3 (loadA 5 6) 6 = s 6 := by
    rw [srun_untouched k 6 (loadA 5 6) (by decide +kernel) t3]
    exact hc0_6aa
  have ho2_14a : srun k t3 (loadA 5 6) 14 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [srun_untouched k 14 (loadA 5 6) (by decide +kernel) t3]
    exact ho2_14
  have ho2_15a : srun k t3 (loadA 5 6) 15 = Mont2.wsel (s 13) (s 8) (s 10) := by
    rw [srun_untouched k 15 (loadA 5 6) (by decide +kernel) t3]
    exact ho2_15
  have ho3_16 : srun k t3 (loadA 5 6) 16 = s 5 := by
    rw [lf61 k t3, hc0_5aa]
  have ho3_17 : srun k t3 (loadA 5 6) 17 = s 6 := by
    rw [lf62 k t3, hc0_6aa]
  clear hc0_2aa hc0_3aa hc0_4aa hc0_5aa hc0_6aa ho2_14 ho2_15
  generalize hg3 : srun k t3 (loadA 5 6) = t4 at hc0_2aaa hc0_3aaa hc0_4aaa hc0_5aaa hc0_6aaa ho2_14a ho2_15a ho3_16 ho3_17 ⊢
  clear hg3
  have hc0_2aaaa : srun k t4 (loadB 5 6) 2 = s 2 := by
    rw [srun_untouched k 2 (loadB 5 6) (by decide +kernel) t4]
    exact hc0_2aaa
  have hc0_3aaaa : srun k t4 (loadB 5 6) 3 = s 3 := by
    rw [srun_untouched k 3 (loadB 5 6) (by decide +kernel) t4]
    exact hc0_3aaa
  have hc0_4aaaa : srun k t4 (loadB 5 6) 4 = s 4 := by
    rw [srun_untouched k 4 (loadB 5 6) (by decide +kernel) t4]
    exact hc0_4aaa
  have ho2_14aa : srun k t4 (loadB 5 6) 14 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [srun_untouched k 14 (loadB 5 6) (by decide +kernel) t4]
    exact ho2_14a
  have ho2_15aa : srun k t4 (loadB 5 6) 15 = Mont2.wsel (s 13) (s 8) (s 10) := by
    rw [srun_untouched k 15 (loadB 5 6) (by decide +kernel) t4]
    exact ho2_15a
  have ho3_16a : srun k t4 (loadB 5 6) 16 = s 5 := by
    rw [srun_untouched k 16 (loadB 5 6) (by decide +kernel) t4]
    exact ho3_16
  have ho3_17a : srun k t4 (loadB 5 6) 17 = s 6 := by
    rw [srun_untouched k 17 (loadB 5 6) (by decide +kernel) t4]
    exact ho3_17
  have ho4_18 : srun k t4 (loadB 5 6) 18 = s 5 := by
    rw [lf63 k t4, hc0_5aaa]
  have ho4_19 : srun k t4 (loadB 5 6) 19 = s 6 := by
    rw [lf64 k t4, hc0_6aaa]
  clear hc0_2aaa hc0_3aaa hc0_4aaa hc0_5aaa hc0_6aaa ho2_14a ho2_15a ho3_16 ho3_17
  generalize hg4 : srun k t4 (loadB 5 6) = t5 at hc0_2aaaa hc0_3aaaa hc0_4aaaa ho2_14aa ho2_15aa ho3_16a ho3_17a ho4_18 ho4_19 ⊢
  clear hg4
  have hc0_2aaaaa : srun k t5 (mmBlock) 2 = s 2 := by
    rw [srun_untouched k 2 (mmBlock) (by decide +kernel) t5]
    exact hc0_2aaaa
  have hc0_3aaaaa : srun k t5 (mmBlock) 3 = s 3 := by
    rw [srun_untouched k 3 (mmBlock) (by decide +kernel) t5]
    exact hc0_3aaaa
  have hc0_4aaaaa : srun k t5 (mmBlock) 4 = s 4 := by
    rw [srun_untouched k 4 (mmBlock) (by decide +kernel) t5]
    exact hc0_4aaaa
  have ho2_14aaa : srun k t5 (mmBlock) 14 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [srun_untouched k 14 (mmBlock) (by decide +kernel) t5]
    exact ho2_14aa
  have ho2_15aaa : srun k t5 (mmBlock) 15 = Mont2.wsel (s 13) (s 8) (s 10) := by
    rw [srun_untouched k 15 (mmBlock) (by decide +kernel) t5]
    exact ho2_15aa
  have ho5_267 : srun k t5 (mmBlock) 267 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1 := by
    rw [(mmBlock_spec k t5).1, hc0_2aaaa, hc0_3aaaa, hc0_4aaaa, ho3_16a, ho3_17a, ho4_18, ho4_19]
  have ho5_271 : srun k t5 (mmBlock) 271 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2 := by
    rw [(mmBlock_spec k t5).2, hc0_2aaaa, hc0_3aaaa, hc0_4aaaa, ho3_16a, ho3_17a, ho4_18, ho4_19]
  clear hc0_2aaaa hc0_3aaaa hc0_4aaaa ho2_14aa ho2_15aa ho3_16a ho3_17a ho4_18 ho4_19
  generalize hg5 : srun k t5 (mmBlock) = t6 at hc0_2aaaaa hc0_3aaaaa hc0_4aaaaa ho2_14aaa ho2_15aaa ho5_267 ho5_271 ⊢
  clear hg5
  have hc0_2aaaaaa : srun k t6 (storeC 5 6) 2 = s 2 := by
    rw [srun_untouched k 2 (storeC 5 6) (by decide +kernel) t6]
    exact hc0_2aaaaa
  have hc0_3aaaaaa : srun k t6 (storeC 5 6) 3 = s 3 := by
    rw [srun_untouched k 3 (storeC 5 6) (by decide +kernel) t6]
    exact hc0_3aaaaa
  have hc0_4aaaaaa : srun k t6 (storeC 5 6) 4 = s 4 := by
    rw [srun_untouched k 4 (storeC 5 6) (by decide +kernel) t6]
    exact hc0_4aaaaa
  have ho2_14aaaa : srun k t6 (storeC 5 6) 14 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [srun_untouched k 14 (storeC 5 6) (by decide +kernel) t6]
    exact ho2_14aaa
  have ho2_15aaaa : srun k t6 (storeC 5 6) 15 = Mont2.wsel (s 13) (s 8) (s 10) := by
    rw [srun_untouched k 15 (storeC 5 6) (by decide +kernel) t6]
    exact ho2_15aaa
  have ho6_5 : srun k t6 (storeC 5 6) 5 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1 := by
    rw [lf65 k t6, ho5_267]
  have ho6_6 : srun k t6 (storeC 5 6) 6 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2 := by
    rw [lf66 k t6, ho5_271]
  clear hc0_2aaaaa hc0_3aaaaa hc0_4aaaaa ho2_14aaa ho2_15aaa ho5_267 ho5_271
  generalize hg6 : srun k t6 (storeC 5 6) = t7 at hc0_2aaaaaa hc0_3aaaaaa hc0_4aaaaaa ho6_5 ho6_6 ho2_14aaaa ho2_15aaaa ⊢
  clear hg6
  have hc0_2aaaaaaa : srun k t7 (loadA 5 6) 2 = s 2 := by
    rw [srun_untouched k 2 (loadA 5 6) (by decide +kernel) t7]
    exact hc0_2aaaaaa
  have hc0_3aaaaaaa : srun k t7 (loadA 5 6) 3 = s 3 := by
    rw [srun_untouched k 3 (loadA 5 6) (by decide +kernel) t7]
    exact hc0_3aaaaaa
  have hc0_4aaaaaaa : srun k t7 (loadA 5 6) 4 = s 4 := by
    rw [srun_untouched k 4 (loadA 5 6) (by decide +kernel) t7]
    exact hc0_4aaaaaa
  have ho2_14aaaaa : srun k t7 (loadA 5 6) 14 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [srun_untouched k 14 (loadA 5 6) (by decide +kernel) t7]
    exact ho2_14aaaa
  have ho2_15aaaaa : srun k t7 (loadA 5 6) 15 = Mont2.wsel (s 13) (s 8) (s 10) := by
    rw [srun_untouched k 15 (loadA 5 6) (by decide +kernel) t7]
    exact ho2_15aaaa
  have ho7_16 : srun k t7 (loadA 5 6) 16 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1 := by
    rw [lf61 k t7, ho6_5]
  have ho7_17 : srun k t7 (loadA 5 6) 17 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2 := by
    rw [lf62 k t7, ho6_6]
  clear hc0_2aaaaaa hc0_3aaaaaa hc0_4aaaaaa ho6_5 ho6_6 ho2_14aaaa ho2_15aaaa
  generalize hg7 : srun k t7 (loadA 5 6) = t8 at hc0_2aaaaaaa hc0_3aaaaaaa hc0_4aaaaaaa ho2_14aaaaa ho2_15aaaaa ho7_16 ho7_17 ⊢
  clear hg7
  have hc0_2aaaaaaaa : srun k t8 (loadB 14 15) 2 = s 2 := by
    rw [srun_untouched k 2 (loadB 14 15) (by decide +kernel) t8]
    exact hc0_2aaaaaaa
  have hc0_3aaaaaaaa : srun k t8 (loadB 14 15) 3 = s 3 := by
    rw [srun_untouched k 3 (loadB 14 15) (by decide +kernel) t8]
    exact hc0_3aaaaaaa
  have hc0_4aaaaaaaa : srun k t8 (loadB 14 15) 4 = s 4 := by
    rw [srun_untouched k 4 (loadB 14 15) (by decide +kernel) t8]
    exact hc0_4aaaaaaa
  have ho7_16a : srun k t8 (loadB 14 15) 16 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1 := by
    rw [srun_untouched k 16 (loadB 14 15) (by decide +kernel) t8]
    exact ho7_16
  have ho7_17a : srun k t8 (loadB 14 15) 17 = (Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2 := by
    rw [srun_untouched k 17 (loadB 14 15) (by decide +kernel) t8]
    exact ho7_17
  have ho8_18 : srun k t8 (loadB 14 15) 18 = Mont2.wsel (s 13) (s 7) (s 9) := by
    rw [lf67 k t8, ho2_14aaaaa]
  have ho8_19 : srun k t8 (loadB 14 15) 19 = Mont2.wsel (s 13) (s 8) (s 10) := by
    rw [lf68 k t8, ho2_15aaaaa]
  clear hc0_2aaaaaaa hc0_3aaaaaaa hc0_4aaaaaaa ho2_14aaaaa ho2_15aaaaa ho7_16 ho7_17
  generalize hg8 : srun k t8 (loadB 14 15) = t9 at hc0_2aaaaaaaa hc0_3aaaaaaaa hc0_4aaaaaaaa ho7_16a ho7_17a ho8_18 ho8_19 ⊢
  clear hg8
  have ho9_267 : srun k t9 (mmBlock) 267 = (Mont2.montMul2 (s 2) (s 3) (s 4) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2) (Mont2.wsel (s 13) (s 7) (s 9)) (Mont2.wsel (s 13) (s 8) (s 10))).1 := by
    rw [(mmBlock_spec k t9).1, hc0_2aaaaaaaa, hc0_3aaaaaaaa, hc0_4aaaaaaaa, ho7_16a, ho7_17a, ho8_18, ho8_19]
  have ho9_271 : srun k t9 (mmBlock) 271 = (Mont2.montMul2 (s 2) (s 3) (s 4) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2) (Mont2.wsel (s 13) (s 7) (s 9)) (Mont2.wsel (s 13) (s 8) (s 10))).2 := by
    rw [(mmBlock_spec k t9).2, hc0_2aaaaaaaa, hc0_3aaaaaaaa, hc0_4aaaaaaaa, ho7_16a, ho7_17a, ho8_18, ho8_19]
  clear hc0_2aaaaaaaa hc0_3aaaaaaaa hc0_4aaaaaaaa ho7_16a ho7_17a ho8_18 ho8_19
  generalize hg9 : srun k t9 (mmBlock) = t10 at ho9_267 ho9_271 ⊢
  clear hg9
  have ho10_5 : srun k t10 (storeC 5 6) 5 = (Mont2.montMul2 (s 2) (s 3) (s 4) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2) (Mont2.wsel (s 13) (s 7) (s 9)) (Mont2.wsel (s 13) (s 8) (s 10))).1 := by
    rw [lf65 k t10, ho9_267]
  have ho10_6 : srun k t10 (storeC 5 6) 6 = (Mont2.montMul2 (s 2) (s 3) (s 4) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).1) ((Mont2.montMul2 (s 2) (s 3) (s 4) (s 5) (s 6) (s 5) (s 6)).2) (Mont2.wsel (s 13) (s 7) (s 9)) (Mont2.wsel (s 13) (s 8) (s 10))).2 := by
    rw [lf66 k t10, ho9_271]
  clear ho9_267 ho9_271
  generalize hg10 : srun k t10 (storeC 5 6) = t11 at ho10_5 ho10_6 ⊢
  clear hg10
  exact ⟨ho10_5, ho10_6⟩


/-! ## The loop's register-level step

`srun` is the body's total meaning; `srun_correct` makes it the body's
denotation, so the `FoldBridge` hypotheses are discharged by `decide`.
-/

theorem bodyTail_noDiv : ∀ i ∈ bodyTail, NoDivI i = true := by decide +kernel

theorem body_noDiv (kbits : Nat) : ∀ i ∈ bodyInstrs kbits, NoDivI i = true := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · simp only [bodyHead, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> rfl
  · exact bodyTail_noDiv i h

theorem init_noDiv (n k a : Nat) : ∀ i ∈ initInstrs n k a, NoDivI i = true := by
  intro i hi
  simp only [initInstrs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem epi_noDiv : ∀ i ∈ epiInstrs, NoDivI i = true := by decide +kernel

/--
**The program is a fold** — no `Option`, no CCIR, no trace.  Free of any
arithmetic content: `srun_correct` turns each block's denotation into its
total `Nat`-level meaning, and `FoldBridge` does the rest.
-/
theorem prothProgram_denote_fold (n kbits k a : Nat) :
    (prothProgram n kbits k a).denote =
      some (srun 0
        ((List.range (kbits + (n - 1))).foldl
          (fun s i => srun i s (bodyInstrs kbits))
          (srun 0 initialState (initInstrs n k a)))
        epiInstrs 0) :=
  FoldBridge.Program.denote_eq_foldl (prothProgram n kbits k a)
    (fun _ => True)
    (fun i s => srun i s (bodyInstrs kbits))
    (fun s => srun 0 s epiInstrs)
    (srun 0 initialState (initInstrs n k a))
    (srun_correct 0 (initInstrs n k a) (init_noDiv n k a) initialState)
    trivial
    (fun i s _ => srun_correct i (bodyInstrs kbits) (body_noDiv kbits) s)
    (fun _ _ _ => trivial)
    (fun s _ => srun_correct 0 epiInstrs epi_noDiv s)

/-! ## The Montgomery-domain loop state -/

/-- The register-level step, as arithmetic on the three quantities the
loop actually carries: the exponent-bit window and the accumulator. -/
def stepTriple (kbits n0 n1 np ab0 ab1 one0 one1 : Nat)
    (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let bit := Mont2.wshr t.1 (kbits - 1)
  let w := Mont2.wand (Mont2.wshl t.1 1) (2 ^ kbits - 1)
  let m0 := Mont2.wsel bit ab0 one0
  let m1 := Mont2.wsel bit ab1 one1
  let sq := Mont2.montMul2 n0 n1 np t.2.1 t.2.2 t.2.1 t.2.2
  let pr := Mont2.montMul2 n0 n1 np sq.1 sq.2 m0 m1
  (w, pr.1, pr.2)

/-- The registers that must hold the setup constants for the body to mean
what `stepTriple` says. -/
def SetupOK (n k a : Nat) (s : RegState) : Prop :=
  s 2 = n0Of n k ∧ s 3 = n1Of n k ∧ s 4 = npOf n k ∧
    s 7 = abarOf n k a % 2 ^ 64 ∧ s 8 = abarOf n k a / 2 ^ 64 ∧
    s 9 = oneOf n k % 2 ^ 64 ∧ s 10 = oneOf n k / 2 ^ 64 ∧
    s 11 = tgtOf n k % 2 ^ 64 ∧ s 12 = tgtOf n k / 2 ^ 64

/-! ### The head of the body

The head is the only part of the program whose *literals* mention `kbits`,
so its specification carries the hypothesis `kbits ≤ 64` that makes those
literals fit in a word.
-/

theorem bodyHead_13 (k kbits : Nat) (s : RegState) :
    srun k s (bodyHead kbits) 13 = Mont2.wshr (s 1) ((kbits - 1) % M) := rfl

theorem bodyHead_1 (k kbits : Nat) (s : RegState) :
    srun k s (bodyHead kbits) 1
      = Mont2.wand (Mont2.wshl (s 1) 1) ((2 ^ kbits - 1) % M) := rfl

theorem bodyHead_dest (kbits : Nat) :
    ∀ i ∈ bodyHead kbits, sdest i = 13 ∨ sdest i = 22 ∨ sdest i = 1 := by
  intro i hi
  simp only [bodyHead, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem bodyHead_frame (k kbits : Nat) (s : RegState) (r : Nat)
    (h13 : r ≠ 13) (h22 : r ≠ 22) (h1 : r ≠ 1) :
    srun k s (bodyHead kbits) r = s r :=
  srun_untouched k r (bodyHead kbits)
    (fun i hi => by rcases bodyHead_dest kbits i hi with h | h | h <;> omega) s

theorem bodyTail_dest :
    ∀ i ∈ bodyTail, sdest i = 5 ∨ sdest i = 6 ∨ 13 ≤ sdest i := by decide +kernel

theorem bodyTail_frame (k : Nat) (s : RegState) (r : Nat)
    (hr : r < 13) (h5 : r ≠ 5) (h6 : r ≠ 6) : srun k s bodyTail r = s r :=
  srun_untouched k r bodyTail
    (fun i hi => by rcases bodyTail_dest i hi with h | h | h <;> omega) s

/-- With `kbits ≤ 64` the two `kbits`-dependent literals are already words. -/
theorem kbits_lits (kbits : Nat) (hk : kbits ≤ 64) :
    (kbits - 1) % M = kbits - 1 ∧ (2 ^ kbits - 1) % M = 2 ^ kbits - 1 := by
  have hM : M = 18446744073709551616 := Mont2.M_val
  have hp : 2 ^ kbits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide +kernel
  refine ⟨Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩

/--
**The body computes `stepTriple`.**  This is where the 505-instruction
block meets the arithmetic: proved by composing the leaf blocks' `rfl`
specifications through `srun_append`, never by unfolding the body.
-/
theorem body_step (n kbits k a : Nat) (hkb : kbits ≤ 64) (idx : Nat)
    (s : RegState) (hs : SetupOK n k a s) :
    (srun idx s (bodyInstrs kbits) 1,
        srun idx s (bodyInstrs kbits) 5,
        srun idx s (bodyInstrs kbits) 6) =
      stepTriple kbits (n0Of n k) (n1Of n k) (npOf n k)
        (abarOf n k a % 2 ^ 64) (abarOf n k a / 2 ^ 64)
        (oneOf n k % 2 ^ 64) (oneOf n k / 2 ^ 64)
        (s 1, s 5, s 6) := by
  obtain ⟨e2, e3, e4, e7, e8, e9, e10, _, _⟩ := hs
  obtain ⟨hm1, hm2⟩ := kbits_lits kbits hkb
  rw [bodyInstrs]
  simp only [srun_append]
  have f13 : srun idx s (bodyHead kbits) 13 = Mont2.wshr (s 1) (kbits - 1) := by
    rw [bodyHead_13, hm1]
  have f1 : srun idx s (bodyHead kbits) 1
      = Mont2.wand (Mont2.wshl (s 1) 1) (2 ^ kbits - 1) := by
    rw [bodyHead_1, hm2]
  have g2 : srun idx s (bodyHead kbits) 2 = n0Of n k := by
    rw [bodyHead_frame idx kbits s 2 (by omega) (by omega) (by omega)]; exact e2
  have g3 : srun idx s (bodyHead kbits) 3 = n1Of n k := by
    rw [bodyHead_frame idx kbits s 3 (by omega) (by omega) (by omega)]; exact e3
  have g4 : srun idx s (bodyHead kbits) 4 = npOf n k := by
    rw [bodyHead_frame idx kbits s 4 (by omega) (by omega) (by omega)]; exact e4
  have g5 : srun idx s (bodyHead kbits) 5 = s 5 :=
    bodyHead_frame idx kbits s 5 (by omega) (by omega) (by omega)
  have g6 : srun idx s (bodyHead kbits) 6 = s 6 :=
    bodyHead_frame idx kbits s 6 (by omega) (by omega) (by omega)
  have g7 : srun idx s (bodyHead kbits) 7 = abarOf n k a % 2 ^ 64 := by
    rw [bodyHead_frame idx kbits s 7 (by omega) (by omega) (by omega)]; exact e7
  have g8 : srun idx s (bodyHead kbits) 8 = abarOf n k a / 2 ^ 64 := by
    rw [bodyHead_frame idx kbits s 8 (by omega) (by omega) (by omega)]; exact e8
  have g9 : srun idx s (bodyHead kbits) 9 = oneOf n k % 2 ^ 64 := by
    rw [bodyHead_frame idx kbits s 9 (by omega) (by omega) (by omega)]; exact e9
  have g10 : srun idx s (bodyHead kbits) 10 = oneOf n k / 2 ^ 64 := by
    rw [bodyHead_frame idx kbits s 10 (by omega) (by omega) (by omega)]; exact e10
  generalize hsig : srun idx s (bodyHead kbits) = σ at f13 f1 g2 g3 g4 g5 g6 g7 g8 g9 g10 ⊢
  clear hsig
  have b1 : srun idx σ bodyTail 1 = σ 1 :=
    bodyTail_frame idx σ 1 (by omega) (by omega) (by omega)
  obtain ⟨b5, b6⟩ := bodyTail_spec idx σ
  rw [b1, b5, b6, f1, f13, g2, g3, g4, g5, g6, g7, g8, g9, g10]
  rfl

/-- The body preserves the setup registers. -/
theorem body_setup (n kbits k a : Nat) (idx : Nat) (s : RegState)
    (hs : SetupOK n k a s) : SetupOK n k a (srun idx s (bodyInstrs kbits)) := by
  have key : ∀ r, r < 13 → r ≠ 5 → r ≠ 6 → r ≠ 1 →
      srun idx s (bodyInstrs kbits) r = s r := by
    intro r hr h5 h6 h1
    rw [bodyInstrs, srun_append,
      bodyTail_frame idx (srun idx s (bodyHead kbits)) r hr h5 h6,
      bodyHead_frame idx kbits s r (by omega) (by omega) h1]
  obtain ⟨e2, e3, e4, e7, e8, e9, e10, e11, e12⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [key 2 (by omega) (by omega) (by omega) (by omega)]; exact e2
  · rw [key 3 (by omega) (by omega) (by omega) (by omega)]; exact e3
  · rw [key 4 (by omega) (by omega) (by omega) (by omega)]; exact e4
  · rw [key 7 (by omega) (by omega) (by omega) (by omega)]; exact e7
  · rw [key 8 (by omega) (by omega) (by omega) (by omega)]; exact e8
  · rw [key 9 (by omega) (by omega) (by omega) (by omega)]; exact e9
  · rw [key 10 (by omega) (by omega) (by omega) (by omega)]; exact e10
  · rw [key 11 (by omega) (by omega) (by omega) (by omega)]; exact e11
  · rw [key 12 (by omega) (by omega) (by omega) (by omega)]; exact e12

/-! ## The bridge -/

theorem bodyTail_wf : ∀ i ∈ bodyTail, i.WF regCount := by decide +kernel

theorem epi_wf : ∀ i ∈ epiInstrs, i.WF regCount := by decide +kernel

/-- Well-formedness: program-sized and decidable. -/
theorem prothProgram_wf (n kbits k a : Nat) :
    (prothProgram n kbits k a).WF := by
  refine ⟨?_, ?_, ?_, epi_wf⟩
  · show (0 : Nat) < regCount
    decide
  · show ∀ i ∈ initInstrs n k a, i.WF regCount
    intro i hi
    simp only [initInstrs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact ⟨by decide, trivial⟩
  · show ∀ i ∈ bodyInstrs kbits, i.WF regCount
    intro i hi
    rcases List.mem_append.mp hi with h | h
    · simp only [bodyHead, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> exact ⟨by decide, by decide, trivial⟩
    · exact bodyTail_wf i h

/-! ## Arithmetic of the setup constants

Everything the Montgomery layer needs about `N = k·2ⁿ + 1`: it is odd, the
closed-form multiplier really is a Montgomery multiplier, its two limbs
recover it, and `R mod N`, `a·R mod N`, `(N−1)·R mod N` are the Montgomery
forms of `1`, `a`, `N − 1`.
-/

private theorem dvd_of_add_eq {b X Y S : Nat} (h : X + b * Y = b * S) : b ∣ X := by
  refine ⟨S - Y, ?_⟩
  have hmul : b * (S - Y) = b * S - b * Y := Nat.mul_sub b S Y
  omega

private theorem mul_swap4 (a b c d : Nat) : a * b * (c * d) = a * c * (b * d) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm b c d]

theorem prothN_pos (n k : Nat) : 0 < prothN n k := by
  show 0 < k * 2 ^ n + 1; omega

theorem prothN_odd (n k : Nat) (hn : 1 ≤ n) : prothN n k % 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show (k * 2 ^ (m + 1) + 1) % 2 = 1
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (k * 2 ^ m) 2, Nat.mul_add_mod]

theorem RR_eq : RR = Montgomery.B ^ 2 := by decide +kernel

theorem pval_limbs (n k : Nat) :
    Mont2.pval (n0Of n k) (n1Of n k) = prothN n k := by
  show prothN n k % 2 ^ 64 + 2 ^ 64 * (prothN n k / 2 ^ 64) = prothN n k
  have h := Nat.div_add_mod (prothN n k) (2 ^ 64)
  omega

theorem npOf_spec (n k : Nat) (hn : 32 ≤ n) :
    Montgomery.MontMultiplier (prothN n k) (npOf n k) := by
  obtain ⟨u, hu⟩ : ∃ u, (2 : Nat) ^ n = 2 ^ 32 * u := Nat.pow_dvd_pow 2 hn
  have ht0 : k * 2 ^ n = 2 ^ 32 * (k * u) := by rw [hu, Nat.mul_left_comm]
  show ((k * 2 ^ n + 1) * ((k * 2 ^ n + (2 ^ 64 - 1)) % 2 ^ 64) + 1) % 2 ^ 64 = 0
  generalize hcc : k * 2 ^ n = c at ht0 ⊢
  generalize k * u = t at ht0
  have hq : 2 ^ 64 * ((c + (2 ^ 64 - 1)) / 2 ^ 64) + (c + (2 ^ 64 - 1)) % 2 ^ 64
      = c + (2 ^ 64 - 1) := Nat.div_add_mod _ _
  generalize hrr : (c + (2 ^ 64 - 1)) % 2 ^ 64 = r at hq ⊢
  generalize (c + (2 ^ 64 - 1)) / 2 ^ 64 = q at hq
  obtain ⟨z, hz⟩ : (2 : Nat) ^ 64 ∣ ((c + 1) * r + 1) := by
    refine dvd_of_add_eq (Y := (c + 1) * q) (S := t * t + (c + 1)) ?_
    have E1 : (c + 1) * (c + (2 ^ 64 - 1))
        = (c + 1) * (2 ^ 64 * q) + (c + 1) * r := by rw [← hq, Nat.mul_add]
    have E2 : (c + 1) * (2 ^ 64 * q) = 2 ^ 64 * ((c + 1) * q) :=
      Nat.mul_left_comm _ _ _
    have E3 : (c + 1) * (c + (2 ^ 64 - 1))
        = (c + 1) * c + (c + 1) * (2 ^ 64 - 1) := Nat.mul_add _ _ _
    have E4 : (c + 1) * c = c * c + c := by rw [Nat.add_mul, Nat.one_mul]
    have E5 : (c + 1) * (2 ^ 64 - 1) = (c + 1) * 2 ^ 64 - (c + 1) * 1 :=
      Nat.mul_sub _ _ _
    have E6 : (c + 1) * 2 ^ 64 = 2 ^ 64 * (c + 1) := Nat.mul_comm _ _
    have E7 : c * c = 2 ^ 64 * (t * t) := by
      rw [ht0, mul_swap4, show (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 from by decide +kernel]
    have E8 : (c + 1) * 1 ≤ (c + 1) * 2 ^ 64 :=
      Nat.mul_le_mul (Nat.le_refl _) (by decide)
    have E9 : 2 ^ 64 * (t * t + (c + 1)) = 2 ^ 64 * (t * t) + 2 ^ 64 * (c + 1) :=
      Nat.mul_add _ _ _
    omega
  rw [hz, Nat.mul_mod_right]

theorem oneOf_lt (n k : Nat) : oneOf n k < prothN n k :=
  Nat.mod_lt _ (prothN_pos n k)

theorem oneOf_pos (n k : Nat) (hn : 1 ≤ n) (hbig : 2 ^ 64 < prothN n k) :
    0 < oneOf n k := by
  rcases Nat.eq_zero_or_pos (oneOf n k) with h | h
  · exfalso
    have hdvd : prothN n k ∣ 2 ^ 128 * 1 := by
      rw [Nat.mul_one]; exact Nat.dvd_of_mod_eq_zero h
    have h2 : prothN n k ∣ 1 :=
      Montgomery.dvd_of_odd_dvd_two_pow_mul (prothN_odd n k hn) 128 1 hdvd
    have h3 := Nat.le_of_dvd (by omega) h2
    have h4 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide +kernel
    omega
  · exact h

theorem oneOf_rep (n k : Nat) : Montgomery.Rep 2 (prothN n k) 1 (oneOf n k) := by
  refine ⟨oneOf_lt n k, ?_⟩
  show RR % prothN n k % prothN n k = 1 * Montgomery.B ^ 2 % prothN n k
  rw [Nat.mod_mod, Nat.one_mul, RR_eq]

theorem abarOf_rep (n k a : Nat) :
    Montgomery.Rep 2 (prothN n k) a (abarOf n k a) := by
  refine ⟨Nat.mod_lt _ (prothN_pos n k), ?_⟩
  show a * RR % prothN n k % prothN n k = a * Montgomery.B ^ 2 % prothN n k
  rw [Nat.mod_mod, RR_eq]

theorem tgtOf_lt (n k : Nat) (hn : 1 ≤ n) (hbig : 2 ^ 64 < prothN n k) :
    tgtOf n k < prothN n k := by
  have h := oneOf_pos n k hn hbig
  show prothN n k - oneOf n k < prothN n k
  omega

theorem tgtOf_rep (n k : Nat) (hn : 1 ≤ n) (hbig : 2 ^ 64 < prothN n k) :
    Montgomery.Rep 2 (prothN n k) (prothN n k - 1) (tgtOf n k) := by
  have hpos := oneOf_pos n k hn hbig
  have hlt := oneOf_lt n k
  have hN : 0 < prothN n k := prothN_pos n k
  have htlt := tgtOf_lt n k hn hbig
  refine ⟨htlt, ?_⟩
  rw [Nat.mod_eq_of_lt htlt, ← RR_eq, Nat.mul_mod,
    Nat.mod_eq_of_lt (show prothN n k - 1 < prothN n k by omega)]
  show prothN n k - oneOf n k
      = (prothN n k - 1) * (oneOf n k) % prothN n k
  have e1 : (prothN n k - 1) * oneOf n k
      = prothN n k * oneOf n k - 1 * oneOf n k := Nat.sub_mul _ _ _
  have e2 : prothN n k * (oneOf n k - 1)
      = prothN n k * oneOf n k - prothN n k * 1 := Nat.mul_sub _ _ _
  have e3 : 1 * oneOf n k ≤ prothN n k * oneOf n k :=
    Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have e4 : prothN n k * 1 ≤ prothN n k * oneOf n k :=
    Nat.mul_le_mul (Nat.le_refl _) hpos
  have key : (prothN n k - 1) * oneOf n k
      = (prothN n k - oneOf n k) + prothN n k * (oneOf n k - 1) := by omega
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-! ## The Montgomery-domain loop

The loop's whole content is the invariant: after `j` steps the window holds
`k·2ʲ mod 2^kbits` and the accumulator is the Montgomery form of
`a` raised to the *top `j` bits* of the exponent, which is
`k·2ʲ / 2^kbits`.
-/

private theorem mod_pow_mod (x p q : Nat) (h : p ≤ q) :
    x % 2 ^ q % 2 ^ p = x % 2 ^ p :=
  Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 h)

private theorem wshr_val (x y : Nat) (hx : x < M) : Mont2.wshr x y = x / 2 ^ y := by
  show (x >>> y) % M = x / 2 ^ y
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)

private theorem window_step (kbits w : Nat) (hk64 : kbits ≤ 64) :
    Mont2.wand (Mont2.wshl w 1) (2 ^ kbits - 1) = w * 2 % 2 ^ kbits := by
  have hMv : M = 2 ^ 64 := rfl
  have hshl : Mont2.wshl w 1 = w * 2 % M := by
    show (w <<< 1) % M = w * 2 % M
    rw [Nat.shiftLeft_eq, Nat.pow_one]
  rw [hshl]
  show ((w * 2 % M) &&& (2 ^ kbits - 1)) % M = w * 2 % 2 ^ kbits
  rw [Nat.and_two_pow_sub_one_eq_mod, hMv, mod_pow_mod _ _ _ hk64]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (hMv ▸ Nat.pow_le_pow_right (by omega) hk64))

private theorem shift_mod (x n : Nat) : x % n * 2 % n = x * 2 % n := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

private theorem mul_mod_left (x y n : Nat) : x % n * y % n = x * y % n := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- The exponent bookkeeping of one square-and-multiply step. -/
private theorem exp_step (kbits x : Nat) (hk : 1 ≤ kbits) :
    x * 2 / 2 ^ kbits
      = 2 * (x / 2 ^ kbits) + x % 2 ^ kbits / 2 ^ (kbits - 1) := by
  obtain ⟨p, rfl⟩ : ∃ p, kbits = p + 1 := ⟨kbits - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hdm : 2 ^ (p + 1) * (x / 2 ^ (p + 1)) + x % 2 ^ (p + 1) = x :=
    Nat.div_add_mod _ _
  have hsw : 2 ^ (p + 1) * (2 * (x / 2 ^ (p + 1)))
      = 2 * (2 ^ (p + 1) * (x / 2 ^ (p + 1))) := Nat.mul_left_comm _ _ _
  have hx2 : x * 2
      = x % 2 ^ (p + 1) * 2 + 2 ^ (p + 1) * (2 * (x / 2 ^ (p + 1))) := by omega
  rw [hx2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.pow_succ,
    Nat.mul_div_mul_right _ _ (by omega), Nat.add_comm]

theorem limbs_of_lt (v : Nat) (hv : v < 2 ^ 127) :
    v % 2 ^ 64 < M ∧ v / 2 ^ 64 < M ∧
      Mont2.pval (v % 2 ^ 64) (v / 2 ^ 64) = v := by
  have hM : M = 18446744073709551616 := Mont2.M_val
  have h127 : (2 : Nat) ^ 127
      = 170141183460469231731687303715884105728 := by decide +kernel
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide +kernel
  have hd := Nat.div_add_mod v (2 ^ 64)
  have hm : v % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by omega)
  refine ⟨by omega, by omega, ?_⟩
  show v % 2 ^ 64 + M * (v / 2 ^ 64) = v
  rw [Mont2.M_val]
  omega

/-- Everything the two-limb Montgomery layer needs, in one place. -/
theorem setup_facts (n k : Nat) (hn : 32 ≤ n) (hwide : prothN n k < 2 ^ 127)
    (hbig : 2 ^ 64 < prothN n k) :
    n0Of n k < M ∧ n1Of n k < M ∧ npOf n k < M ∧
      Mont2.pval (n0Of n k) (n1Of n k) = prothN n k ∧
      prothN n k % 2 = 1 ∧ 0 < prothN n k ∧ 2 * prothN n k ≤ M * M ∧
      Montgomery.MontMultiplier (prothN n k) (npOf n k) ∧
      prothN n k ≤ Montgomery.B ^ 2 := by
  have h127 : (2 : Nat) ^ 127
      = 170141183460469231731687303715884105728 := by decide +kernel
  have hMM : M * M = 340282366920938463463374607431768211456 := by decide +kernel
  have hB : Montgomery.B ^ 2
      = 340282366920938463463374607431768211456 := by decide +kernel
  obtain ⟨h0, h1, _⟩ := limbs_of_lt (prothN n k) hwide
  refine ⟨h0, h1, Nat.mod_lt _ (by decide), pval_limbs n k,
    prothN_odd n k (by omega), prothN_pos n k, ?_, npOf_spec n k hn, ?_⟩
  · rw [hMM]; omega
  · rw [hB]; omega

/-- One Montgomery multiplication of represented values, at the limb level. -/
theorem mm2_rep (n k : Nat) (hn : 32 ≤ n) (hwide : prothN n k < 2 ^ 127)
    (hbig : 2 ^ 64 < prothN n k) (x y u0 u1 v0 v1 : Nat)
    (hu0 : u0 < M) (hu1 : u1 < M) (hv0 : v0 < M) (hv1 : v1 < M)
    (hu : Montgomery.Rep 2 (prothN n k) x (Mont2.pval u0 u1))
    (hv : Montgomery.Rep 2 (prothN n k) y (Mont2.pval v0 v1)) :
    Montgomery.Rep 2 (prothN n k) (x * y)
        (Mont2.pval
          (Mont2.montMul2 (n0Of n k) (n1Of n k) (npOf n k) u0 u1 v0 v1).1
          (Mont2.montMul2 (n0Of n k) (n1Of n k) (npOf n k) u0 u1 v0 v1).2) ∧
      (Mont2.montMul2 (n0Of n k) (n1Of n k) (npOf n k) u0 u1 v0 v1).1 < M ∧
      (Mont2.montMul2 (n0Of n k) (n1Of n k) (npOf n k) u0 u1 v0 v1).2 < M := by
  obtain ⟨hn0, hn1, hnp, hpv, hodd, hNpos, hHalf, hinv, hNR⟩ :=
    setup_facts n k hn hwide hbig
  have hval := Mont2.montMul2_val (n0Of n k) (n1Of n k) (npOf n k) u0 u1 v0 v1
    hn0 hn1 hnp hu0 hu1 hv0 hv1 (by rw [hpv]; exact hodd) (by rw [hpv]; exact hNpos)
    (by rw [hpv]; exact hHalf) (by rw [hpv]; exact hinv)
    (by rw [hpv]; exact hu.1) (by rw [hpv]; exact hv.1)
  rw [hpv] at hval
  refine ⟨?_, hval.2.1, hval.2.2⟩
  rw [hval.1]
  exact Montgomery.montMul_rep 2 (prothN n k) (npOf n k) hinv hodd hNpos hNR
    x y _ _ hu hv

/-- The register loop's step, as a function of the three carried values. -/
def stepT (n kbits k a : Nat) : Nat × Nat × Nat → Nat × Nat × Nat :=
  stepTriple kbits (n0Of n k) (n1Of n k) (npOf n k)
    (abarOf n k a % 2 ^ 64) (abarOf n k a / 2 ^ 64)
    (oneOf n k % 2 ^ 64) (oneOf n k / 2 ^ 64)

/-- `m` steps. -/
def iterT (n kbits k a : Nat) : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, t => t
  | m + 1, t => iterT n kbits k a m (stepT n kbits k a t)

/-- The loop invariant after `j` steps. -/
def LoopInv (n kbits k a j : Nat) (t : Nat × Nat × Nat) : Prop :=
  t.1 = k * 2 ^ j % 2 ^ kbits ∧ t.2.1 < M ∧ t.2.2 < M ∧
    Montgomery.Rep 2 (prothN n k) (a ^ (k * 2 ^ j / 2 ^ kbits))
      (Mont2.pval t.2.1 t.2.2)

/-- The squared accumulator of one step. -/
def sqOf (n k : Nat) (t : Nat × Nat × Nat) : Nat × Nat :=
  Mont2.montMul2 (n0Of n k) (n1Of n k) (npOf n k) t.2.1 t.2.2 t.2.1 t.2.2

/-- The branchlessly selected multiplier of one step. -/
def selOf (n kbits k a : Nat) (t : Nat × Nat × Nat) : Nat × Nat :=
  (Mont2.wsel (Mont2.wshr t.1 (kbits - 1)) (abarOf n k a % 2 ^ 64)
      (oneOf n k % 2 ^ 64),
   Mont2.wsel (Mont2.wshr t.1 (kbits - 1)) (abarOf n k a / 2 ^ 64)
      (oneOf n k / 2 ^ 64))

theorem stepT_eq (n kbits k a : Nat) (t : Nat × Nat × Nat) :
    stepT n kbits k a t
      = (Mont2.wand (Mont2.wshl t.1 1) (2 ^ kbits - 1),
         (Mont2.montMul2 (n0Of n k) (n1Of n k) (npOf n k) (sqOf n k t).1
            (sqOf n k t).2 (selOf n kbits k a t).1 (selOf n kbits k a t).2).1,
         (Mont2.montMul2 (n0Of n k) (n1Of n k) (npOf n k) (sqOf n k t).1
            (sqOf n k t).2 (selOf n kbits k a t).1 (selOf n kbits k a t).2).2) :=
  rfl

theorem stepT_inv (n kbits k a : Nat) (hn : 32 ≤ n) (hk1 : 1 ≤ kbits)
    (hk64 : kbits ≤ 64) (hwide : prothN n k < 2 ^ 127)
    (hbig : 2 ^ 64 < prothN n k) (j : Nat) (t : Nat × Nat × Nat)
    (h : LoopInv n kbits k a j t) :
    LoopInv n kbits k a (j + 1) (stepT n kbits k a t) := by
  obtain ⟨hw, hc0, hc1, hrep⟩ := h
  have hMv : M = 2 ^ 64 := rfl
  have hpk : (2 : Nat) ^ kbits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk64
  have hwlt : t.1 < 2 ^ kbits := by rw [hw]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hwM : t.1 < M := by rw [hMv]; omega
  have hsplit : (2 : Nat) ^ kbits = 2 ^ (kbits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have hbitv : Mont2.wshr t.1 (kbits - 1) = t.1 / 2 ^ (kbits - 1) :=
    wshr_val _ _ hwM
  have hbit2 : t.1 / 2 ^ (kbits - 1) < 2 :=
    Nat.div_lt_of_lt_mul (by rw [← hsplit]; exact hwlt)
  have hpj : k * 2 ^ (j + 1) = k * 2 ^ j * 2 := by
    rw [Nat.pow_succ, Nat.mul_assoc]
  have hexp : k * 2 ^ (j + 1) / 2 ^ kbits
      = 2 * (k * 2 ^ j / 2 ^ kbits) + t.1 / 2 ^ (kbits - 1) := by
    rw [hpj, exp_step kbits _ hk1, hw]
  have hwin : Mont2.wand (Mont2.wshl t.1 1) (2 ^ kbits - 1)
      = k * 2 ^ (j + 1) % 2 ^ kbits := by
    rw [window_step kbits t.1 hk64, hw, shift_mod, hpj]
  obtain ⟨hab0, hab1, habp⟩ :=
    limbs_of_lt (abarOf n k a) (Nat.lt_trans (Nat.mod_lt _ (prothN_pos n k)) hwide)
  obtain ⟨hon0, hon1, honp⟩ :=
    limbs_of_lt (oneOf n k) (Nat.lt_trans (oneOf_lt n k) hwide)
  have hsq : Montgomery.Rep 2 (prothN n k)
        (a ^ (k * 2 ^ j / 2 ^ kbits) * a ^ (k * 2 ^ j / 2 ^ kbits))
        (Mont2.pval (sqOf n k t).1 (sqOf n k t).2) ∧
      (sqOf n k t).1 < M ∧ (sqOf n k t).2 < M :=
    mm2_rep n k hn hwide hbig _ _ t.2.1 t.2.2 t.2.1 t.2.2 hc0 hc1 hc0 hc1 hrep hrep
  have hsel : ∃ y, Montgomery.Rep 2 (prothN n k) y
        (Mont2.pval (selOf n kbits k a t).1 (selOf n kbits k a t).2) ∧
      (selOf n kbits k a t).1 < M ∧ (selOf n kbits k a t).2 < M ∧
      a ^ (k * 2 ^ (j + 1) / 2 ^ kbits)
        = a ^ (k * 2 ^ j / 2 ^ kbits) * a ^ (k * 2 ^ j / 2 ^ kbits) * y := by
    rcases (show t.1 / 2 ^ (kbits - 1) = 0 ∨ t.1 / 2 ^ (kbits - 1) = 1 by omega)
      with hb | hb
    · have e0 : (selOf n kbits k a t).1 = oneOf n k % 2 ^ 64 := by
        show Mont2.wsel (Mont2.wshr t.1 (kbits - 1)) (abarOf n k a % 2 ^ 64)
          (oneOf n k % 2 ^ 64) = oneOf n k % 2 ^ 64
        rw [hbitv, hb]; exact Mont2.wsel_zero _ _ hon0
      have e1 : (selOf n kbits k a t).2 = oneOf n k / 2 ^ 64 := by
        show Mont2.wsel (Mont2.wshr t.1 (kbits - 1)) (abarOf n k a / 2 ^ 64)
          (oneOf n k / 2 ^ 64) = oneOf n k / 2 ^ 64
        rw [hbitv, hb]; exact Mont2.wsel_zero _ _ hon1
      refine ⟨1, ?_, by rw [e0]; exact hon0, by rw [e1]; exact hon1, ?_⟩
      · rw [e0, e1, honp]; exact oneOf_rep n k
      · rw [hexp, hb, Nat.mul_one,
          show 2 * (k * 2 ^ j / 2 ^ kbits) + 0
            = k * 2 ^ j / 2 ^ kbits + k * 2 ^ j / 2 ^ kbits from by omega,
          Nat.pow_add]
    · have e0 : (selOf n kbits k a t).1 = abarOf n k a % 2 ^ 64 := by
        show Mont2.wsel (Mont2.wshr t.1 (kbits - 1)) (abarOf n k a % 2 ^ 64)
          (oneOf n k % 2 ^ 64) = abarOf n k a % 2 ^ 64
        rw [hbitv, hb]; exact Mont2.wsel_one _ _ hab0
      have e1 : (selOf n kbits k a t).2 = abarOf n k a / 2 ^ 64 := by
        show Mont2.wsel (Mont2.wshr t.1 (kbits - 1)) (abarOf n k a / 2 ^ 64)
          (oneOf n k / 2 ^ 64) = abarOf n k a / 2 ^ 64
        rw [hbitv, hb]; exact Mont2.wsel_one _ _ hab1
      refine ⟨a, ?_, by rw [e0]; exact hab0, by rw [e1]; exact hab1, ?_⟩
      · rw [e0, e1, habp]; exact abarOf_rep n k a
      · rw [hexp, hb,
          show 2 * (k * 2 ^ j / 2 ^ kbits) + 1
            = k * 2 ^ j / 2 ^ kbits + k * 2 ^ j / 2 ^ kbits + 1 from by omega,
          Nat.pow_succ, Nat.pow_add]
  obtain ⟨y, hyrep, hy0, hy1, hpow⟩ := hsel
  have hpr := mm2_rep n k hn hwide hbig _ y (sqOf n k t).1 (sqOf n k t).2
    (selOf n kbits k a t).1 (selOf n kbits k a t).2
    hsq.2.1 hsq.2.2 hy0 hy1 hsq.1 hyrep
  rw [stepT_eq]
  exact ⟨hwin, hpr.2.1, hpr.2.2, by rw [hpow]; exact hpr.1⟩

theorem iterT_inv (n kbits k a : Nat) (hn : 32 ≤ n) (hk1 : 1 ≤ kbits)
    (hk64 : kbits ≤ 64) (hwide : prothN n k < 2 ^ 127)
    (hbig : 2 ^ 64 < prothN n k) :
    ∀ (m j : Nat) (t : Nat × Nat × Nat), LoopInv n kbits k a j t →
      LoopInv n kbits k a (j + m) (iterT n kbits k a m t) := by
  intro m
  induction m with
  | zero => intro j t h; exact h
  | succ m ih =>
      intro j t h
      have h2 := ih (j + 1) _ (stepT_inv n kbits k a hn hk1 hk64 hwide hbig j t h)
      rw [show j + 1 + m = j + (m + 1) from by omega] at h2
      exact h2

theorem stepT_def (n kbits k a : Nat) (t : Nat × Nat × Nat) :
    stepTriple kbits (n0Of n k) (n1Of n k) (npOf n k)
        (abarOf n k a % 2 ^ 64) (abarOf n k a / 2 ^ 64)
        (oneOf n k % 2 ^ 64) (oneOf n k / 2 ^ 64) t = stepT n kbits k a t := rfl

/-- **The register loop is `iterT`.** -/
theorem loop_fold (n kbits k a : Nat) (hk64 : kbits ≤ 64) :
    ∀ (L : List Nat) (s : RegState), SetupOK n k a s →
      SetupOK n k a
          (L.foldl (fun s i => srun i s (bodyInstrs kbits)) s) ∧
        ((L.foldl (fun s i => srun i s (bodyInstrs kbits)) s) 1,
          (L.foldl (fun s i => srun i s (bodyInstrs kbits)) s) 5,
          (L.foldl (fun s i => srun i s (bodyInstrs kbits)) s) 6)
          = iterT n kbits k a L.length (s 1, s 5, s 6) := by
  intro L
  induction L with
  | nil => intro s hs; exact ⟨hs, rfl⟩
  | cons d L ih =>
      intro s hs
      have hstep := body_step n kbits k a hk64 d s hs
      rw [stepT_def] at hstep
      have h := ih (srun d s (bodyInstrs kbits)) (body_setup n kbits k a d s hs)
      refine ⟨h.1, ?_⟩
      show ((L.foldl (fun s i => srun i s (bodyInstrs kbits))
              (srun d s (bodyInstrs kbits))) 1,
            (L.foldl (fun s i => srun i s (bodyInstrs kbits))
              (srun d s (bodyInstrs kbits))) 5,
            (L.foldl (fun s i => srun i s (bodyInstrs kbits))
              (srun d s (bodyInstrs kbits))) 6)
          = iterT n kbits k a L.length (stepT n kbits k a (s 1, s 5, s 6))
      rw [← hstep]
      exact h.2

/-! ### The initial state -/

theorem denoteOperand_lit (idx v : Nat) (s : RegState) :
    Reflect.denoteOperand idx s (Operand.lit v) = v % M := rfl

/--
Reading back a `mov` of a literal, *without* ever reducing the literal:
`npOf n k` contains `2⁶⁴ − 1`, and asking the kernel to add that to a
symbolic `k·2ⁿ` would make it unfold `Nat.add` a literal-many times.  The
frame lemma keeps the literal opaque.
-/
theorem srun_lit_val (idx : Nat) (s : RegState) (pre post : List Instr)
    (d v : Nat) (ds : List Nat) (hds : post.map sdest = ds)
    (hd : ∀ x ∈ ds, x ≠ d) :
    srun idx s (pre ++ Instr.mov d (Operand.lit v) :: post) d = v % M := by
  have hpost : ∀ i ∈ post, sdest i ≠ d := fun i hi =>
    hd (sdest i) (by rw [← hds]; exact List.mem_map.mpr ⟨i, hi, rfl⟩)
  rw [srun_append, srun_cons, srun_untouched idx d post hpost]
  show (if d = d then Reflect.denoteOperand idx (srun idx s pre) (Operand.lit v)
        else srun idx s pre d) = v % M
  rw [if_pos rfl]
  exact denoteOperand_lit idx v _


theorem init_r1 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 1 = (k) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 0)
    ((initInstrs n k a).drop 1) 1 (k)
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] rfl (by decide)

theorem init_r2 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 2 = (n0Of n k) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 1)
    ((initInstrs n k a).drop 2) 2 (n0Of n k)
    [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] rfl (by decide)

theorem init_r3 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 3 = (n1Of n k) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 2)
    ((initInstrs n k a).drop 3) 3 (n1Of n k)
    [4, 5, 6, 7, 8, 9, 10, 11, 12] rfl (by decide)

theorem init_r4 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 4 = (npOf n k) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 3)
    ((initInstrs n k a).drop 4) 4 (npOf n k)
    [5, 6, 7, 8, 9, 10, 11, 12] rfl (by decide)

theorem init_r5 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 5 = (oneOf n k % 2 ^ 64) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 4)
    ((initInstrs n k a).drop 5) 5 (oneOf n k % 2 ^ 64)
    [6, 7, 8, 9, 10, 11, 12] rfl (by decide)

theorem init_r6 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 6 = (oneOf n k / 2 ^ 64) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 5)
    ((initInstrs n k a).drop 6) 6 (oneOf n k / 2 ^ 64)
    [7, 8, 9, 10, 11, 12] rfl (by decide)

theorem init_r7 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 7 = (abarOf n k a % 2 ^ 64) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 6)
    ((initInstrs n k a).drop 7) 7 (abarOf n k a % 2 ^ 64)
    [8, 9, 10, 11, 12] rfl (by decide)

theorem init_r8 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 8 = (abarOf n k a / 2 ^ 64) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 7)
    ((initInstrs n k a).drop 8) 8 (abarOf n k a / 2 ^ 64)
    [9, 10, 11, 12] rfl (by decide)

theorem init_r9 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 9 = (oneOf n k % 2 ^ 64) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 8)
    ((initInstrs n k a).drop 9) 9 (oneOf n k % 2 ^ 64)
    [10, 11, 12] rfl (by decide)

theorem init_r10 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 10 = (oneOf n k / 2 ^ 64) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 9)
    ((initInstrs n k a).drop 10) 10 (oneOf n k / 2 ^ 64)
    [11, 12] rfl (by decide)

theorem init_r11 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 11 = (tgtOf n k % 2 ^ 64) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 10)
    ((initInstrs n k a).drop 11) 11 (tgtOf n k % 2 ^ 64)
    [12] rfl (by decide)

theorem init_r12 (n k a : Nat) :
    srun 0 initialState (initInstrs n k a) 12 = (tgtOf n k / 2 ^ 64) % M :=
  srun_lit_val 0 initialState ((initInstrs n k a).take 11)
    ((initInstrs n k a).drop 12) 12 (tgtOf n k / 2 ^ 64)
    [] rfl (by decide)

theorem init_facts (n kbits k a : Nat) (hn : 32 ≤ n) (hk64 : kbits ≤ 64)
    (hkw : k < 2 ^ kbits) (hwide : prothN n k < 2 ^ 127)
    (hbig : 2 ^ 64 < prothN n k) :
    SetupOK n k a (srun 0 initialState (initInstrs n k a)) ∧
      srun 0 initialState (initInstrs n k a) 1 = k ∧
      srun 0 initialState (initInstrs n k a) 5 = oneOf n k % 2 ^ 64 ∧
      srun 0 initialState (initInstrs n k a) 6 = oneOf n k / 2 ^ 64 := by
  have r1 := init_r1 n k a
  have r2 := init_r2 n k a
  have r3 := init_r3 n k a
  have r4 := init_r4 n k a
  have r5 := init_r5 n k a
  have r6 := init_r6 n k a
  have r7 := init_r7 n k a
  have r8 := init_r8 n k a
  have r9 := init_r9 n k a
  have r10 := init_r10 n k a
  have r11 := init_r11 n k a
  have r12 := init_r12 n k a
  obtain ⟨hn0, hn1, hnp, hpv, hodd, hNpos, hHalf, hinv, hNR⟩ :=
    setup_facts n k hn hwide hbig
  obtain ⟨ho0, ho1, _⟩ :=
    limbs_of_lt (oneOf n k) (Nat.lt_trans (oneOf_lt n k) hwide)
  obtain ⟨ha0, ha1, _⟩ :=
    limbs_of_lt (abarOf n k a) (Nat.lt_trans (Nat.mod_lt _ (prothN_pos n k)) hwide)
  have htw : tgtOf n k < 2 ^ 127 := by
    have : tgtOf n k = prothN n k - oneOf n k := rfl
    omega
  obtain ⟨ht0, ht1, _⟩ := limbs_of_lt (tgtOf n k) htw
  have hkM : k < M := by
    have : (2 : Nat) ^ kbits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hk64
    show k < 2 ^ 64
    omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [r2, Nat.mod_eq_of_lt hn0]
  · rw [r3, Nat.mod_eq_of_lt hn1]
  · rw [r4, Nat.mod_eq_of_lt hnp]
  · rw [r7, Nat.mod_eq_of_lt ha0]
  · rw [r8, Nat.mod_eq_of_lt ha1]
  · rw [r9, Nat.mod_eq_of_lt ho0]
  · rw [r10, Nat.mod_eq_of_lt ho1]
  · rw [r11, Nat.mod_eq_of_lt ht0]
  · rw [r12, Nat.mod_eq_of_lt ht1]
  · rw [r1, Nat.mod_eq_of_lt hkM]
  · rw [r5, Nat.mod_eq_of_lt ho0]
  · rw [r6, Nat.mod_eq_of_lt ho1]

/-! ### The epilogue -/

theorem epi_val (s : RegState) :
    srun 0 s epiInstrs 0 = if s 5 = s 11 ∧ s 6 = s 12 then 0 else 1 := by
  have e : srun 0 s epiInstrs 0
      = Mont2.wsub 1 (Mont2.wand (if s 5 = s 11 then 1 else 0)
          (if s 6 = s 12 then 1 else 0)) := rfl
  rw [e]
  by_cases h1 : s 5 = s 11
  · by_cases h2 : s 6 = s 12
    · rw [if_pos h1, if_pos h2, if_pos (⟨h1, h2⟩ : s 5 = s 11 ∧ s 6 = s 12)]
      decide +kernel
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
      decide +kernel
  · by_cases h2 : s 6 = s 12
    · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]
      decide +kernel
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1)]
      decide +kernel

theorem pval_inj (x0 x1 y0 y1 : Nat) (hx0 : x0 < M) (hy0 : y0 < M)
    (h : Mont2.pval x0 x1 = Mont2.pval y0 y1) : x0 = y0 ∧ x1 = y1 := by
  have hM : M = 18446744073709551616 := Mont2.M_val
  have h' : x0 + M * x1 = y0 + M * y1 := h
  rw [hM] at h' hx0 hy0
  omega

/--
**The bridge.**  The program's denotation is `0` exactly when the witness
`a` certifies `N = k·2ⁿ + 1` by Proth's criterion.  Combined with the
exit-code contract of the emitted `main`, the artifact exits `0` exactly on
that congruence.
-/
theorem prothProgram_denote (n kbits k a : Nat)
    (hn : 32 ≤ n) (hk64 : kbits ≤ 64) (hkb : 0 < k) (hkw : k < 2 ^ kbits)
    (hwide : prothN n k < 2 ^ 127) (hbig : 2 ^ 64 < prothN n k)
    (ha : 0 < a) :
    (prothProgram n kbits k a).denote =
      some (if a ^ ((prothN n k - 1) / 2) % prothN n k = prothN n k - 1
            then 0 else 1) := by
  have hk1 : 1 ≤ kbits := by
    rcases Nat.eq_zero_or_pos kbits with hz | hz
    · subst hz
      rw [Nat.pow_zero] at hkw
      omega
    · exact hz
  obtain ⟨hn0M, hn1M, hnpM, hpv, hodd, hNpos, hHalf, hinv, hNR⟩ :=
    setup_facts n k hn hwide hbig
  obtain ⟨hsetup, hi1, hi5, hi6⟩ := init_facts n kbits k a hn hk64 hkw hwide hbig
  obtain ⟨hon0, hon1, honp⟩ :=
    limbs_of_lt (oneOf n k) (Nat.lt_trans (oneOf_lt n k) hwide)
  have hinv0 : LoopInv n kbits k a 0
      (srun 0 initialState (initInstrs n k a) 1,
        srun 0 initialState (initInstrs n k a) 5,
        srun 0 initialState (initInstrs n k a) 6) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show srun 0 initialState (initInstrs n k a) 1 = k * 2 ^ 0 % 2 ^ kbits
      rw [hi1, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hkw]
    · show srun 0 initialState (initInstrs n k a) 5 < M
      rw [hi5]; exact hon0
    · show srun 0 initialState (initInstrs n k a) 6 < M
      rw [hi6]; exact hon1
    · show Montgomery.Rep 2 (prothN n k) (a ^ (k * 2 ^ 0 / 2 ^ kbits))
        (Mont2.pval (srun 0 initialState (initInstrs n k a) 5)
          (srun 0 initialState (initInstrs n k a) 6))
      rw [hi5, hi6, honp, Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hkw,
        Nat.pow_zero]
      exact oneOf_rep n k
  obtain ⟨hsetF, hfoldF⟩ := loop_fold n kbits k a hk64
    (List.range (kbits + (n - 1))) (srun 0 initialState (initInstrs n k a)) hsetup
  rw [List.length_range] at hfoldF
  rw [prothProgram_denote_fold, epi_val]
  generalize hSF : (List.range (kbits + (n - 1))).foldl
      (fun s i => srun i s (bodyInstrs kbits))
      (srun 0 initialState (initInstrs n k a)) = sF at hsetF hfoldF ⊢
  clear hSF
  have hfin := iterT_inv n kbits k a hn hk1 hk64 hwide hbig (kbits + (n - 1)) 0 _ hinv0
  rw [← hfoldF, Nat.zero_add] at hfin
  obtain ⟨-, h5M, h6M, hrepF⟩ := hfin
  have hE : k * 2 ^ (kbits + (n - 1)) / 2 ^ kbits = k * 2 ^ (n - 1) := by
    rw [Nat.pow_add, Nat.mul_left_comm,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  have hhalf : (prothN n k - 1) / 2 = k * 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    show (k * 2 ^ (m + 1) + 1 - 1) / 2 = k * 2 ^ m
    rw [Nat.pow_succ, ← Nat.mul_assoc,
      show k * 2 ^ m * 2 + 1 - 1 = k * 2 ^ m * 2 from by omega,
      Nat.mul_div_cancel _ (by omega)]
  rw [hE, ← hhalf] at hrepF
  have htw : tgtOf n k < 2 ^ 127 := by
    have e : tgtOf n k = prothN n k - oneOf n k := rfl
    omega
  obtain ⟨htg0, htg1, htgp⟩ := limbs_of_lt (tgtOf n k) htw
  have htgrep := tgtOf_rep n k (by omega) hbig
  obtain ⟨-, -, -, -, -, -, -, e11, e12⟩ := hsetF
  rw [e11, e12]
  have hiff : (sF 5 = tgtOf n k % 2 ^ 64 ∧ sF 6 = tgtOf n k / 2 ^ 64)
      ↔ a ^ ((prothN n k - 1) / 2) % prothN n k = prothN n k - 1 := by
    constructor
    · intro hq
      have hpvEq : Mont2.pval (sF 5) (sF 6) = tgtOf n k := by
        rw [hq.1, hq.2, htgp]
      have h1 : (a ^ ((prothN n k - 1) / 2) * Montgomery.B ^ 2) % prothN n k
          = ((prothN n k - 1) * Montgomery.B ^ 2) % prothN n k := by
        rw [← hrepF.2, ← htgrep.2, hpvEq]
      have h2 := Montgomery.cancel_B_pow (prothN n k) hodd 2 _ _ h1
      rwa [Nat.mod_eq_of_lt (show prothN n k - 1 < prothN n k by omega)] at h2
    · intro hc
      have e1 : Mont2.pval (sF 5) (sF 6) % prothN n k
          = tgtOf n k % prothN n k := by
        rw [hrepF.2, htgrep.2, ← mul_mod_left, hc]
      rw [Nat.mod_eq_of_lt hrepF.1, Nat.mod_eq_of_lt htgrep.1] at e1
      exact pval_inj (sF 5) (sF 6) (tgtOf n k % 2 ^ 64) (tgtOf n k / 2 ^ 64)
        h5M htg0 (by rw [e1, htgp])
  have hmain :
      (if sF 5 = tgtOf n k % 2 ^ 64 ∧ sF 6 = tgtOf n k / 2 ^ 64 then 0 else 1)
        = (if a ^ ((prothN n k - 1) / 2) % prothN n k = prothN n k - 1
           then 0 else 1) := by
    by_cases hc : a ^ ((prothN n k - 1) / 2) % prothN n k = prothN n k - 1
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (fun hx => hc (hiff.mp hx)), if_neg hc]
  rw [hmain]

end LeanCompCert.Ports.TGProth

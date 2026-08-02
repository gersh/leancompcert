namespace LeanCompCert.CCIR

/-- Machine-level types used at the LCNF/CompCert boundary. -/
inductive CCType where
  | void
  | u8 | u16 | u32 | u64 | usize
  | i8 | i16 | i32 | i64 | isize
  | f32 | f64
  | obj
  | ptr (element : CCType)
  | fnPtr (args : Array CCType) (result : CCType)
  deriving Repr, Inhabited

/-
Equality is written out rather than derived.

`deriving BEq` on an inductive that nests through `Array` compiles to
well-founded recursion, which the kernel does not unfold — and the CCIR and C
validators compare types constantly, so a derived instance is on its own enough
to make `Attest.Artifact.source?` unevaluable by `decide +kernel`.  The
definition below is the derived one, with the `Array` comparison spelled out as
a structural walk over `.toList`; it accepts exactly the same pairs.
-/
mutual
/-- Structural equality on machine types. -/
def CCType.beq : CCType → CCType → Bool
  | .void, .void => true
  | .u8, .u8 => true
  | .u16, .u16 => true
  | .u32, .u32 => true
  | .u64, .u64 => true
  | .usize, .usize => true
  | .i8, .i8 => true
  | .i16, .i16 => true
  | .i32, .i32 => true
  | .i64, .i64 => true
  | .isize, .isize => true
  | .f32, .f32 => true
  | .f64, .f64 => true
  | .obj, .obj => true
  | .ptr left, .ptr right => CCType.beq left right
  | .fnPtr leftArgs leftResult, .fnPtr rightArgs rightResult =>
      CCType.beqList leftArgs.toList rightArgs.toList && CCType.beq leftResult rightResult
  | _, _ => false

/-- Pointwise equality of two type lists, including their lengths. -/
def CCType.beqList : List CCType → List CCType → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      CCType.beq left right && CCType.beqList leftRest rightRest
  | _, _ => false
end

instance : BEq CCType := ⟨CCType.beq⟩

def CCType.bitWidth (pointerBits : Nat := 64) : CCType → Option Nat
  | .u8 | .i8 => some 8
  | .u16 | .i16 => some 16
  | .u32 | .i32 | .f32 => some 32
  | .u64 | .i64 | .f64 => some 64
  | .usize | .isize | .obj | .ptr _ | .fnPtr _ _ => some pointerBits
  | .void => none

def CCType.isUnsigned : CCType → Bool
  | .u8 | .u16 | .u32 | .u64 | .usize => true
  | _ => false

def CCType.isSigned : CCType → Bool
  | .i8 | .i16 | .i32 | .i64 | .isize => true
  | _ => false

def CCType.isInteger (type : CCType) : Bool :=
  type.isUnsigned || type.isSigned

def CCType.isScalar : CCType → Bool
  | .void => false
  | .fnPtr _ _ => true
  | _ => true

/-
Rendering a type.

Structural, not `partial`: the recursion under `fnPtr` goes through the
companion `CCType.toStringList` on `args.toList`, which is a projection of the
constructor argument.  The kernel therefore unfolds this, which is what makes
`CCIR.validateProgram` — and hence `Attest.Artifact.source?` — evaluable by
`decide +kernel`.  `CCType.toStringList` is `List.map CCType.toString`, so the
rendered text is unchanged.
-/
mutual
/-- Render a type. -/
def CCType.toString : CCType → String
  | .void => "void"
  | .u8 => "u8"
  | .u16 => "u16"
  | .u32 => "u32"
  | .u64 => "u64"
  | .usize => "usize"
  | .i8 => "i8"
  | .i16 => "i16"
  | .i32 => "i32"
  | .i64 => "i64"
  | .isize => "isize"
  | .f32 => "f32"
  | .f64 => "f64"
  | .obj => "obj"
  | .ptr element => s!"ptr<{element.toString}>"
  | .fnPtr args result =>
      let rendered := String.intercalate ", " (CCType.toStringList args.toList)
      s!"fn({rendered}) -> {result.toString}"

/-- `List.map CCType.toString`, spelled out so the recursion is structural. -/
def CCType.toStringList : List CCType → List String
  | [] => []
  | type :: rest => type.toString :: CCType.toStringList rest
end

theorem CCType.toStringList_eq_map (types : List CCType) :
    CCType.toStringList types = types.map CCType.toString := by
  induction types with
  | nil => rfl
  | cons _ _ ih => simp [CCType.toStringList, ih]

instance : ToString CCType := ⟨CCType.toString⟩

end LeanCompCert.CCIR

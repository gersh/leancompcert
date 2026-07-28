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
  deriving Repr, BEq, Inhabited

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

partial def CCType.toString : CCType → String
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
      let rendered := String.intercalate ", " (args.toList.map CCType.toString)
      s!"fn({rendered}) -> {result.toString}"

instance : ToString CCType := ⟨CCType.toString⟩

end LeanCompCert.CCIR

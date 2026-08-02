namespace LeanCompCert.C

inductive CType where
  | void
  | bool
  | u8 | u16 | u32 | u64 | usize
  | i8 | i16 | i32 | i64 | isize
  | f32 | f64
  | named (name : String)
  | ptr (element : CType)
  | fnPtr (args : Array CType) (result : CType)
  deriving Repr, Inhabited

/-
Equality is written out rather than derived, for the reason given on
`CCIR.CCType.beq`: `deriving BEq` on an inductive nesting through `Array`
compiles to well-founded recursion, which the kernel does not unfold.  This is
the derived definition with the `Array` comparison spelled out structurally,
and accepts exactly the same pairs.
-/
mutual
/-- Structural equality on C types. -/
def CType.beq : CType → CType → Bool
  | .void, .void => true
  | .bool, .bool => true
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
  | .named left, .named right => left == right
  | .ptr left, .ptr right => CType.beq left right
  | .fnPtr leftArgs leftResult, .fnPtr rightArgs rightResult =>
      CType.beqList leftArgs.toList rightArgs.toList && CType.beq leftResult rightResult
  | _, _ => false

/-- Pointwise equality of two type lists, including their lengths. -/
def CType.beqList : List CType → List CType → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      CType.beq left right && CType.beqList leftRest rightRest
  | _, _ => false
end

instance : BEq CType := ⟨CType.beq⟩

def CType.isSigned : CType → Bool
  | .i8 | .i16 | .i32 | .i64 | .isize => true
  | _ => false

def CType.isUnsigned : CType → Bool
  | .u8 | .u16 | .u32 | .u64 | .usize => true
  | _ => false

def CType.isInteger (type : CType) : Bool :=
  type.isSigned || type.isUnsigned || type == .bool

def CType.isPointer : CType → Bool
  | .ptr _ | .fnPtr _ _ => true
  | _ => false

inductive CUnaryOp where
  | bitNot | boolNot | neg
  deriving Repr, BEq, DecidableEq, Inhabited

inductive CBinaryOp where
  | add | sub | mul | div | rem
  | bitAnd | bitOr | bitXor
  | shl | shr
  | eq | ne | lt | le | gt | ge
  | logicalAnd | logicalOr
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Calls and assignments are deliberately absent from expressions. -/
inductive CExpr where
  | var (name : String) (type : CType)
  | uintLit (type : CType) (value : Nat)
  | intLit (type : CType) (value : Int)
  | boolLit (value : Bool)
  | null (type : CType)
  | unary (type : CType) (op : CUnaryOp) (value : CExpr)
  | binary (type : CType) (op : CBinaryOp) (lhs rhs : CExpr)
  | cast (type : CType) (value : CExpr)
  | addressOf (type : CType) (value : CExpr)
  | deref (type : CType) (value : CExpr)
  | field (type : CType) (object : CExpr) (name : String)
  | index (type : CType) (array index : CExpr)
  deriving Repr, BEq, Inhabited

def CExpr.type : CExpr → CType
  | .var _ type | .uintLit type _ | .intLit type _ | .null type
  | .unary type _ _ | .binary type _ _ _ | .cast type _
  | .addressOf type _ | .deref type _ | .field type _ _
  | .index type _ _ => type
  | .boolLit _ => .bool

structure CParam where
  name : String
  type : CType
  deriving Repr, BEq, Inhabited

mutual
inductive CStmt where
  | decl (type : CType) (name : String) (init : Option CExpr := none)
  | assign (target value : CExpr)
  | call
      (destination : Option CExpr)
      (callee : String)
      (args : Array CExpr)
      (resultType : CType)
  | callIndirect
      (destination : Option CExpr)
      (callee : CExpr)
      (signature : CType)
      (args : Array CExpr)
  | ifThenElse (condition : CExpr) (thenBody elseBody : Array CStmt)
  | switch (discriminant : CExpr) (cases : Array CSwitchCase) (default : Option (Array CStmt))
  | whileLoop (condition : CExpr) (body : Array CStmt)
  | goto (label : String)
  | label (label : String)
  | return (value : Option CExpr)
  | unreachable (reason : String)
  | comment (text : String)
  deriving Repr, BEq, Inhabited

structure CSwitchCase where
  value : Nat
  body : Array CStmt
  deriving Repr, BEq, Inhabited
end

structure CFunction where
  name : String
  params : Array CParam
  result : CType
  body : Array CStmt
  internal : Bool := false
  sourceDecl : Option String := none
  deriving Repr, BEq, Inhabited

inductive CGlobalInit where
  | zero
  | uintLit (type : CType) (value : Nat)
  | intLit (type : CType) (value : Int)
  | string (value : String)
  | address (symbol : String)
  deriving Repr, BEq, Inhabited

structure CGlobal where
  name : String
  type : CType
  init : CGlobalInit
  constant : Bool := false
  internal : Bool := true
  deriving Repr, BEq, Inhabited

structure CExternal where
  name : String
  params : Array CType
  result : CType
  trusted : Bool := false
  deriving Repr, BEq, Inhabited

structure CTranslationUnit where
  includes : Array String := #["stdint.h", "stddef.h"]
  externals : Array CExternal := #[]
  globals : Array CGlobal := #[]
  functions : Array CFunction := #[]
  deriving Repr, BEq, Inhabited

end LeanCompCert.C

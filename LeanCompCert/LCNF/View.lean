namespace LeanCompCert.LCNF

/--
A version-stable view of the impure Lean compiler IR.  Only this module's
adapter is allowed to depend directly on Lean's internal LCNF constructors.
-/
inductive ViewType where
  | void
  | erased
  | u8 | u16 | u32 | u64 | usize
  | f32 | f64
  | object
  | tagged
  | taggedObject
  | unknown (description : String)
  deriving Repr, BEq, Inhabited

structure Param where
  id : String
  name : String
  type : ViewType
  borrowed : Bool
  deriving Repr, BEq, Inhabited

inductive Literal where
  | nat (value : Nat)
  | string (value : String)
  | u8 (value : Nat)
  | u16 (value : Nat)
  | u32 (value : Nat)
  | u64 (value : Nat)
  | usize (value : Nat)
  deriving Repr, BEq, Inhabited

inductive Arg where
  | erased
  | local (id : String)
  deriving Repr, BEq, Inhabited

structure CtorInfo where
  name : String
  tag : Nat
  objectFields : Nat
  usizeFields : Nat
  scalarBytes : Nat
  deriving Repr, BEq, Inhabited

inductive ProjectionKind where
  | object (index : Nat)
  | usize (index : Nat)
  | scalar (bytes offset : Nat)
  deriving Repr, BEq, Inhabited

inductive Value where
  | literal (value : Literal)
  | erased
  | localCall (callee : String) (args : Array Arg)
  | directCall (callee : String) (args : Array Arg)
  | partialApply (callee : String) (args : Array Arg)
  | ctor (info : CtorInfo) (args : Array Arg)
  | project (kind : ProjectionKind) (object : String)
  | reset (fieldCount : Nat) (object : String)
  | reuse (object : String) (info : CtorInfo) (updateHeader : Bool) (args : Array Arg)
  | box (type : ViewType) (value : String)
  | unbox (value : String)
  | isShared (value : String)
  | unsupported (description : String)
  deriving Repr, BEq, Inhabited

structure LetDecl where
  id : String
  name : String
  type : ViewType
  value : Value
  deriving Repr, BEq, Inhabited

mutual
inductive Code where
  | letValue (decl : LetDecl) (next : Code)
  | joinPoint (decl : FunDecl) (next : Code)
  | jump (target : String) (args : Array Arg)
  | cases (discriminant : String) (alternatives : Array Alternative)
  | return (value : String)
  | unreachable
  | setObjectField (object : String) (index : Nat) (value : Arg) (next : Code)
  | setUSizeField (object : String) (index : Nat) (value : String) (next : Code)
  | setScalarField
      (object : String) (bytes offset : Nat) (value : String) (type : ViewType) (next : Code)
  | setTag (object : String) (tag : Nat) (next : Code)
  | retain (object : String) (count : Nat) (check persistent : Bool) (next : Code)
  | release
      (object : String)
      (count : Nat)
      (check persistent : Bool)
      (objectFields : Option Nat)
      (next : Code)
  | delete (object : String) (next : Code)
  | unsupported (description : String)
  deriving Repr, Inhabited

structure FunDecl where
  id : String
  name : String
  params : Array Param
  result : ViewType
  body : Code
  deriving Repr, Inhabited

inductive Alternative where
  | constructor (info : CtorInfo) (body : Code)
  | default (body : Code)
  deriving Repr, Inhabited
end

inductive DeclValue where
  | code (body : Code)
  | external
  deriving Repr, Inhabited

structure Decl where
  name : String
  params : Array Param
  result : ViewType
  value : DeclValue
  recursive : Bool
  safe : Bool
  deriving Repr, Inhabited

structure Module where
  compilerVersion : String
  declarations : Array Decl
  deriving Repr, Inhabited

end LeanCompCert.LCNF

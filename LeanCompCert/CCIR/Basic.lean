import LeanCompCert.CCIR.Type

namespace LeanCompCert.CCIR

structure LocalId where
  value : Nat
  deriving Repr, BEq, DecidableEq, Ord, Inhabited

structure BlockId where
  value : Nat
  deriving Repr, BEq, DecidableEq, Ord, Inhabited

structure GlobalId where
  name : String
  deriving Repr, BEq, DecidableEq, Ord, Inhabited

instance : ToString LocalId := ⟨fun id => s!"%{id.value}"⟩
instance : ToString BlockId := ⟨fun id => s!"bb{id.value}"⟩
instance : ToString GlobalId := ⟨fun id => id.name⟩

structure LocalDecl where
  id : LocalId
  type : CCType
  sourceName : Option String := none
  deriving Repr, BEq, Inhabited

inductive Operand where
  | local (id : LocalId)
  | global (id : GlobalId)
  | uintLit (type : CCType) (value : Nat)
  | intLit (type : CCType) (value : Int)
  | null (type : CCType)
  deriving Repr, BEq, Inhabited

inductive UnaryOp where
  | bitNot
  | boolNot
  | neg
  | cast (target : CCType)
  deriving Repr, BEq, Inhabited

inductive BinaryOp where
  | add | sub | mul
  | udiv | urem
  | sdiv | srem
  | bitAnd | bitOr | bitXor
  | shl | lshr | ashr
  | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving Repr, BEq, Inhabited

/-- Effectful operations are statements; operands themselves are pure. -/
inductive Instruction where
  | assign (dest : LocalDecl) (value : Operand)
  | unary (dest : LocalDecl) (op : UnaryOp) (value : Operand)
  | binary (dest : LocalDecl) (op : BinaryOp) (lhs rhs : Operand)
  | load (dest : LocalDecl) (address : Operand)
  | store (address value : Operand)
  /-- Load one element from a typed pointer base.  Unlike `.load`, the address
  is kept as `(base, index)` so lowering never needs to integerize a pointer. -/
  | loadIndex (dest : LocalDecl) (base index : Operand)
  /-- Store one element through a typed pointer base. -/
  | storeIndex (base index value : Operand)
  | call
      (dest : Option LocalDecl)
      (callee : GlobalId)
      (args : Array Operand)
      (resultType : CCType)
  | runtimeCall
      (dest : Option LocalDecl)
      (symbol : String)
      (args : Array Operand)
      (resultType : CCType)
  | retain (value : Operand)
  | release (value : Operand)
  | allocCtor (dest : LocalDecl) (tag fieldCount : Nat)
  | setField (object : Operand) (index : Nat) (value : Operand)
  | getTag (dest : LocalDecl) (object : Operand)
  | project (dest : LocalDecl) (object : Operand) (index : Nat)
  deriving Repr, BEq, Inhabited

def Instruction.destination? : Instruction → Option LocalDecl
  | .assign dest _ | .unary dest _ _ | .binary dest _ _ _
  | .load dest _ | .loadIndex dest _ _ | .allocCtor dest _ _ | .getTag dest _
  | .project dest _ _ => some dest
  | .call dest _ _ _ | .runtimeCall dest _ _ _ => dest
  | .store _ _ | .storeIndex _ _ _ | .setField _ _ _ | .retain _ | .release _ => none

def Instruction.operands : Instruction → Array Operand
  | .assign _ value | .unary _ _ value | .load _ value
  | .retain value | .release value | .getTag _ value => #[value]
  | .binary _ _ lhs rhs | .store lhs rhs | .loadIndex _ lhs rhs => #[lhs, rhs]
  | .storeIndex base index value => #[base, index, value]
  | .call _ _ args _ | .runtimeCall _ _ args _ => args
  | .allocCtor _ _ _ => #[]
  | .setField object _ value => #[object, value]
  | .project _ object _ => #[object]

inductive Terminator where
  | goto (target : BlockId)
  | branch (condition : Operand) (thenBlock elseBlock : BlockId)
  | switch
      (discriminant : Operand)
      (cases : Array (Nat × BlockId))
      (default : Option BlockId)
  | return (value : Option Operand)
  | unreachable (reason : String)
  deriving Repr, BEq, Inhabited

structure Block where
  id : BlockId
  instructions : Array Instruction
  terminator : Terminator
  deriving Repr, BEq, Inhabited

structure Function where
  name : GlobalId
  params : Array LocalDecl
  result : CCType
  entry : BlockId
  blocks : Array Block
  sourceDecl : Option String := none
  deriving Repr, BEq, Inhabited

structure External where
  name : GlobalId
  args : Array CCType
  result : CCType
  trusted : Bool := false
  deriving Repr, BEq, Inhabited

structure Program where
  functions : Array Function
  externals : Array External := #[]
  deriving Repr, BEq, Inhabited

def Function.findBlock? (fn : Function) (id : BlockId) : Option Block :=
  fn.blocks.toList.find? (fun block => block.id == id)

def Program.findFunction? (program : Program) (id : GlobalId) : Option Function :=
  program.functions.toList.find? (fun fn => fn.name == id)

end LeanCompCert.CCIR

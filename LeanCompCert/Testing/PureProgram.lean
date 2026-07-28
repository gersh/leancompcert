import LeanCompCert.CCIR.Interpreter
import LeanCompCert.Lower.Pure

namespace LeanCompCert.Testing

open LeanCompCert.CCIR

private def mkLocal (id : Nat) (type : CCType) : LocalDecl :=
  { id := ⟨id⟩, type }

def addFunction : Function := {
  name := ⟨"Example.add"⟩
  params := #[mkLocal 0 .u64, mkLocal 1 .u64]
  result := .u64
  entry := ⟨0⟩
  blocks := #[{
    id := ⟨0⟩
    instructions := #[
      .binary (mkLocal 2 .u64) .add (.local ⟨0⟩) (.local ⟨1⟩)
    ]
    terminator := .return (some (.local ⟨2⟩))
  }]
  sourceDecl := some "Example.add"
}

/-- A loop-shaped CCIR function exercising bounded-stack tail recursion lowering. -/
def sumToFunction : Function := {
  name := ⟨"Example.sumTo"⟩
  params := #[mkLocal 0 .u64, mkLocal 1 .u64]
  result := .u64
  entry := ⟨0⟩
  blocks := #[
    {
      id := ⟨0⟩
      instructions := #[
        .binary (mkLocal 2 .u8) .eq (.local ⟨0⟩) (.uintLit .u64 0)
      ]
      terminator := .branch (.local ⟨2⟩) ⟨2⟩ ⟨1⟩
    },
    {
      id := ⟨1⟩
      instructions := #[
        .binary (mkLocal 3 .u64) .add (.local ⟨1⟩) (.local ⟨0⟩),
        .binary (mkLocal 4 .u64) .sub (.local ⟨0⟩) (.uintLit .u64 1),
        .assign (mkLocal 0 .u64) (.local ⟨4⟩),
        .assign (mkLocal 1 .u64) (.local ⟨3⟩)
      ]
      terminator := .goto ⟨0⟩
    },
    {
      id := ⟨2⟩
      instructions := #[]
      terminator := .return (some (.local ⟨1⟩))
    }
  ]
  sourceDecl := some "Example.sumTo"
}

def pureProgram : Program := {
  functions := #[addFunction, sumToFunction]
}

def demoMainC : String :=
  "\nint main(void)\n" ++
  "{\n" ++
  "    uint64_t result;\n" ++
  "    result = l_Example_sumTo(UINT64_C(100), UINT64_C(0));\n" ++
  "    if (result == UINT64_C(5050)) {\n" ++
  "        return 0;\n" ++
  "    }\n" ++
  "    return 1;\n" ++
  "}\n"

def emittedDemo : Except (Array String) String := do
  let (_, source) ← Lower.compileProgram .portable pureProgram
  pure (source ++ demoMainC)

end LeanCompCert.Testing

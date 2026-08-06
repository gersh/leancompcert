import LeanCompCert.Ports.MoebiusSawtoothDenote

/-! Emitted-C artifact for the guarded Möbius sawtooth head checker. -/

namespace LeanCompCert.Testing.MoebiusSawtoothCertificate

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.MoebiusSawtooth

def expected : Nat := 0

def symbolName : String := "MoebiusSawtooth.head11815"

def mainC : String :=
  "\nstatic uint64_t cells[" ++ toString program.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "    return l_MoebiusSawtooth_head11815(cells)" ++
  " == UINT64_C(" ++ toString expected ++ ") ? 0 : 1;\n}\n"

def emittedC : Except (Array String) String := do
  let source ← program.emitRolled symbolName
  pure (source ++ mainC)

end LeanCompCert.Testing.MoebiusSawtoothCertificate

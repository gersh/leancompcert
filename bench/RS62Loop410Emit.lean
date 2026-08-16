import LeanCompCert.Ports.RS62CheckpointManifestData
import LeanCompCert.Ports.RS62Loop410Program
import LeanCompCert.Ports.RS62SegmentedPrimeMask
import LeanCompCert.Verified.ArrayAudit

/-! Emit the production segmented-sieve plus equation-(4.10) consumer. -/

open LeanCompCert
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.RS62SegmentedPrimeMask

namespace Bench.RS62Loop410Emit

abbrev bootstrapPrimes : List Nat :=
  LeanCompCert.Ports.RS62CheckpointManifestData.bootstrapPrimes

def cfg (lo segLen rootCap mainCount markSteps : Nat) : Cfg := {
  lo := lo, segLen := segLen, segCount := 1, rootCount := 1
  bootPrimes := bootstrapPrimes, mainCount := mainCount
  rootCap := rootCap, markSteps := markSteps
}

def parseNat (label value : String) : IO Nat := do
  let some n := value.toNat? | throw <| IO.userError s!"bad {label}: {value}"
  return n

def driver (c : Cfg) (bad logL product : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "static uint64_t audit_cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void) {\n" ++
  " uint64_t ma=l_rs62__410__mark__audit((uint64_t*)(uintptr_t)audit_cells);\n" ++
  " uint64_t m=l_rs62__410__mark((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t z=l_rs62__410__normalize((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t ca=l_rs62__410__audit((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t b=l_rs62__410__bad((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t l=l_rs62__410__logl((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t p=l_rs62__410__product((uint64_t*)(uintptr_t)cells);\n" ++
  " printf(\"mark_audit %llu\\nmark %llu\\nnorm %llu\\nconsumer_audit %llu\\nbad %llu\\nlogL %llu\\nproduct %llu\\n\",(unsigned long long)ma,(unsigned long long)m,(unsigned long long)z,(unsigned long long)ca,(unsigned long long)b,(unsigned long long)l,(unsigned long long)p);\n" ++
  " if(ma||ca) return 1;\n" ++
  " if(b!=UINT64_C(" ++ toString bad ++ ")) return 2;\n" ++
  " if(l!=UINT64_C(" ++ toString logL ++ ")) return 3;\n" ++
  " if(p!=UINT64_C(" ++ toString product ++ ")) return 4;\n" ++
  " return 0; }\n"

def runMain (args : List String) : IO UInt32 := do
  match args with
  | [loS, fS, rootS, countS, stepsS, slS, pS, sqrtS, denS, nm2S,
      badS, logS, productS, out] => try
      let lo ← parseNat "lo" loS
      let f ← parseNat "fuel" fS
      let root ← parseNat "rootCap" rootS
      let count ← parseNat "mainCount" countS
      let steps ← parseNat "markSteps" stepsS
      let sl ← parseNat "SL" slS
      let p ← parseNat "P" pS
      let sqrt0 ← parseNat "sqrt" sqrtS
      let den ← parseNat "den" denS
      let nm2 ← parseNat "nm2" nm2S
      let bad ← parseNat "bad" badS
      let logL ← parseNat "expected logL" logS
      let product ← parseNat "expected product" productS
      let c := cfg lo f root count steps
      let mark := LeanCompCert.Ports.RS62SegmentedPrimeMask.program c
      let norm := normalizeProgram f
      let cp outReg := LeanCompCert.Ports.RS62Loop410Program.program
        lo f sl p sqrt0 den nm2 outReg
      let badP := cp LeanCompCert.Ports.RS62Loop410Program.rBad
      match (LeanCompCert.Verified.ArrayAudit.auditProgram mark).emitRolled
          "rs62_410_mark_audit", mark.emitRolled "rs62_410_mark",
          norm.emitRolled "rs62_410_normalize",
          (LeanCompCert.Verified.ArrayAudit.auditProgram badP).emitRolled
            "rs62_410_audit",
          badP.emitRolled "rs62_410_bad",
          (cp LeanCompCert.Ports.RS62Loop410Program.rLogL).emitRolled
            "rs62_410_logl",
          (cp LeanCompCert.Ports.RS62Loop410Program.rP).emitRolled
            "rs62_410_product" with
      | .ok a, .ok m, .ok n, .ok ca, .ok b, .ok l, .ok pOut =>
          IO.FS.writeFile out (a ++ m ++ n ++ ca ++ b ++ l ++ pOut ++
            driver c bad logL product)
          IO.println s!"lo={lo} f={f} rootCap={root} markSteps={steps}"
          IO.println s!"arrayLen={c.arrayLen} bytesPerArray={8 * c.arrayLen}"
          return 0
      | _, _, _, _, _, _, _ =>
          IO.eprintln "C emission failed"
          return 1
    catch e => IO.eprintln e.toString; return 1
  | _ => IO.eprintln "expected 13 numeric arguments and OUT.c"; return 1

end Bench.RS62Loop410Emit

def main (args : List String) : IO UInt32 := Bench.RS62Loop410Emit.runMain args

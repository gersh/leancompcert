import LeanCompCert.Ports.RS62CheckpointManifestData
import LeanCompCert.Ports.RS62Loop314Program
import LeanCompCert.Ports.RS62SegmentedPrimeMask
import LeanCompCert.Verified.ArrayAudit

open LeanCompCert
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.RS62SegmentedPrimeMask

namespace Bench.RS62Loop314Emit

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

def driver (c : Cfg) (bad logL logU accLo accHi : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "static uint64_t audit_cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void) {\n" ++
  " uint64_t ma=l_rs62__314__mark__audit((uint64_t*)(uintptr_t)audit_cells);\n" ++
  " uint64_t m=l_rs62__314__mark((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t z=l_rs62__314__normalize((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t ca=l_rs62__314__audit((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t b=l_rs62__314__bad((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t l=l_rs62__314__logl((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t u=l_rs62__314__logu((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t al=l_rs62__314__acclo((uint64_t*)(uintptr_t)cells);\n" ++
  " uint64_t ah=l_rs62__314__acchi((uint64_t*)(uintptr_t)cells);\n" ++
  " printf(\"mark_audit %llu\\nmark %llu\\nnorm %llu\\nconsumer_audit %llu\\nbad %llu\\nlogL %llu\\nlogU %llu\\naccLo %llu\\naccHi %llu\\n\",(unsigned long long)ma,(unsigned long long)m,(unsigned long long)z,(unsigned long long)ca,(unsigned long long)b,(unsigned long long)l,(unsigned long long)u,(unsigned long long)al,(unsigned long long)ah);\n" ++
  " if(ma||ca) return 1;\n" ++
  " if(b!=UINT64_C(" ++ toString bad ++ ")) return 2;\n" ++
  " if(l!=UINT64_C(" ++ toString logL ++ ")||u!=UINT64_C(" ++ toString logU ++ ")) return 3;\n" ++
  " if(al!=UINT64_C(" ++ toString accLo ++ ")||ah!=UINT64_C(" ++ toString accHi ++ ")) return 4;\n" ++
  " return 0; }\n"

def runMain (args : List String) : IO UInt32 := do
  match args with
  | [loS,fS,rootS,countS,stepsS,slS,suS,ailS,aihS,badS,llS,luS,
      aloS,ahiS,out] => try
      let lo ← parseNat "lo" loS
      let f ← parseNat "fuel" fS
      let root ← parseNat "rootCap" rootS
      let count ← parseNat "mainCount" countS
      let steps ← parseNat "markSteps" stepsS
      let sl ← parseNat "SL" slS
      let su ← parseNat "SU" suS
      let ail ← parseNat "accLo" ailS
      let aih ← parseNat "accHi" aihS
      let bad ← parseNat "bad" badS
      let ll ← parseNat "expected logL" llS
      let lu ← parseNat "expected logU" luS
      let alo ← parseNat "expected accLo" aloS
      let ahi ← parseNat "expected accHi" ahiS
      let c := cfg lo f root count steps
      let mark := program c
      let norm := normalizeProgram f
      let cp outReg := LeanCompCert.Ports.RS62Loop314Program.program
        lo f sl su ail aih outReg
      let badP := cp LeanCompCert.Ports.RS62Loop314Program.rBad
      match (LeanCompCert.Verified.ArrayAudit.auditProgram mark).emitRolled
          "rs62_314_mark_audit", mark.emitRolled "rs62_314_mark",
          norm.emitRolled "rs62_314_normalize",
          (LeanCompCert.Verified.ArrayAudit.auditProgram badP).emitRolled
            "rs62_314_audit",
          badP.emitRolled "rs62_314_bad",
          (cp LeanCompCert.Ports.RS62Loop314Program.rLogL).emitRolled "rs62_314_logl",
          (cp LeanCompCert.Ports.RS62Loop314Program.rLogU).emitRolled "rs62_314_logu",
          (cp LeanCompCert.Ports.RS62Loop314Program.rAccLo).emitRolled "rs62_314_acclo",
          (cp LeanCompCert.Ports.RS62Loop314Program.rAccHi).emitRolled "rs62_314_acchi" with
      | .ok a,.ok m,.ok n,.ok ca,.ok b,.ok l,.ok u,.ok al,.ok ah =>
          IO.FS.writeFile out (a++m++n++ca++b++l++u++al++ah++
            driver c bad ll lu alo ahi)
          IO.println s!"lo={lo} f={f} rootCap={root} markSteps={steps}"
          return 0
      | _,_,_,_,_,_,_,_,_ =>
          IO.eprintln "C emission failed"
          return 1
    catch e => IO.eprintln e.toString; return 1
  | _ => IO.eprintln "expected 14 numeric arguments and OUT.c"; return 1

end Bench.RS62Loop314Emit

def main (args : List String) : IO UInt32 := Bench.RS62Loop314Emit.runMain args

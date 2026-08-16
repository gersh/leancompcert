import LeanCompCert.Ports.RS62CheckpointManifestData
import LeanCompCert.Ports.RS62PrimeMaskLadderOverflow
import LeanCompCert.Verified.ArrayAudit

/-!
Emit the production-shaped RS62 segmented pipeline.

Lean only constructs the verified programs and emits CompCert C.  Prime
marking, zero/nonzero normalization, and both ladder accumulators execute in
the compiled binary.  The separate audited marker is fail-safe evidence that
the partial source marker is defined; the ordinary marker supplies the shared
array consumed by the remaining compiled stages.

The current production schedule uses checkpoint-aligned segments of at most
one million cells.  Its bootstrap bound is 1,000, so the fixed table below is
the complete prime table through 1,000.  Per-segment length, `rootCap`,
`mainCount`, and `markSteps` are explicit command-line literals and are
checked by the formal configuration receipt rather than trusted as emitter
computations.
-/

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.RS62SegmentedPrimeMask

namespace Bench.RS62SegmentedPipelineEmit

abbrev bootstrapPrimes : List Nat :=
  LeanCompCert.Ports.RS62CheckpointManifestData.bootstrapPrimes

def cfg (lo segLen rootCap mainCount markSteps : Nat) : Cfg := {
  lo := lo
  segLen := segLen
  segCount := 1
  rootCount := 1
  bootPrimes := bootstrapPrimes
  mainCount := mainCount
  rootCap := rootCap
  markSteps := markSteps
}

def driver (c : Cfg) (expectedLower expectedUpper : Nat) : String :=
  "\n#include <stdio.h>\n" ++
  "static uint64_t cells[" ++ toString c.arrayLen ++ "];\n" ++
  "static uint64_t audit_cells[" ++ toString c.arrayLen ++ "];\n" ++
  "int main(void)\n{\n" ++
  "  uint64_t audit = l_rs62__mark__audit((uint64_t *)(uintptr_t)audit_cells);\n" ++
  "  uint64_t mark = l_rs62__mark((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t norm = l_rs62__normalize((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t ladder_audit = l_rs62__ladder__audit((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t overflow = l_rs62__ladder__overflow((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t lower = l_rs62__lower((uint64_t *)(uintptr_t)cells);\n" ++
  "  uint64_t upper = l_rs62__upper((uint64_t *)(uintptr_t)cells);\n" ++
  "  printf(\"mark_audit %llu\\nmark %llu\\nnorm %llu\\noverflow %llu\\nladder_audit %llu\\nlower %llu\\nupper %llu\\n\",\n" ++
  "    (unsigned long long)audit, (unsigned long long)mark,\n" ++
  "    (unsigned long long)norm, (unsigned long long)overflow,\n" ++
  "    (unsigned long long)ladder_audit,\n" ++
  "    (unsigned long long)lower,\n" ++
  "    (unsigned long long)upper);\n" ++
  "  if (audit != UINT64_C(0)) return 1;\n" ++
  "  if (overflow != UINT64_C(0)) return 2;\n" ++
  "  if (ladder_audit != UINT64_C(0)) return 3;\n" ++
  "  if (lower != UINT64_C(" ++ toString expectedLower ++ ")) return 4;\n" ++
  "  if (upper != UINT64_C(" ++ toString expectedUpper ++ ")) return 5;\n" ++
  "  return 0;\n}\n"

def parseNat (label value : String) : IO Nat := do
  let some n := value.toNat? | throw <| IO.userError s!"bad {label}: {value}"
  return n

def runMain (args : List String) : IO UInt32 := do
  match args with
  | [loS, segLenS, rootCapS, mainCountS, markStepsS, slS, suS,
      lowerS, upperS, out] =>
      try
        let lo ← parseNat "lo" loS
        let segLen ← parseNat "segLen" segLenS
        let rootCap ← parseNat "rootCap" rootCapS
        let mainCount ← parseNat "mainCount" mainCountS
        let markSteps ← parseNat "markSteps" markStepsS
        let sl ← parseNat "SL" slS
        let su ← parseNat "SU" suS
        let lower ← parseNat "lower" lowerS
        let upper ← parseNat "upper" upperS
        let c := cfg lo segLen rootCap mainCount markSteps
        let mark := program c
        let normalize := normalizeProgram c.segLen
        let overflowProgram :=
          LeanCompCert.Ports.RS62PrimeMaskLadderOverflow.program
            c.lo c.segLen sl su
        let lowerProgram :=
          LeanCompCert.Ports.RS62PrimeMaskLadderOverflow.program
            c.lo c.segLen sl su
            LeanCompCert.Ports.RS62PrimeMaskLadder.rLogL
        let upperProgram :=
          LeanCompCert.Ports.RS62PrimeMaskLadderOverflow.program
            c.lo c.segLen sl su
            LeanCompCert.Ports.RS62PrimeMaskLadder.rLogU
        match (LeanCompCert.Verified.ArrayAudit.auditProgram mark).emitRolled
              "rs62_mark_audit",
            mark.emitRolled "rs62_mark",
            normalize.emitRolled "rs62_normalize",
            overflowProgram.emitRolled "rs62_ladder_overflow",
            (LeanCompCert.Verified.ArrayAudit.auditProgram overflowProgram).emitRolled
              "rs62_ladder_audit",
            lowerProgram.emitRolled "rs62_lower",
            upperProgram.emitRolled "rs62_upper" with
        | .ok markAuditC, .ok markC, .ok normalizeC, .ok overflowC,
          .ok ladderAuditC, .ok lowerC, .ok upperC =>
            IO.FS.writeFile out
              (markAuditC ++ markC ++ normalizeC ++ overflowC ++
                ladderAuditC ++ lowerC ++ upperC ++ driver c lower upper)
            IO.println s!"lo={lo} segLen={c.segLen} hi={c.hi}"
            IO.println s!"rootCap={rootCap} mainCount={mainCount} markSteps={markSteps}"
            IO.println s!"arrayLen={c.arrayLen} bytesPerArray={8 * c.arrayLen}"
            IO.println s!"markLoop={mark.loopCount} ladderLoop={c.segLen}"
            return 0
        | .error errs, _, _, _, _, _, _ | _, .error errs, _, _, _, _, _ |
          _, _, .error errs, _, _, _, _ | _, _, _, .error errs, _, _, _ |
          _, _, _, _, .error errs, _, _ | _, _, _, _, _, .error errs, _ |
          _, _, _, _, _, _, .error errs =>
            for e in errs do IO.eprintln e
            return 1
      catch e =>
        IO.eprintln e.toString
        return 1
  | _ =>
      IO.eprintln
        "usage: LO SEGLEN ROOTCAP MAINCOUNT MARKSTEPS SL SU LOWER UPPER OUT.c"
      return 1

end Bench.RS62SegmentedPipelineEmit

def main (args : List String) : IO UInt32 :=
  Bench.RS62SegmentedPipelineEmit.runMain args

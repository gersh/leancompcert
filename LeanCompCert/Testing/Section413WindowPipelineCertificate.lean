import LeanCompCert.Ports.Section413G1TableProducer
import LeanCompCert.Ports.Section413G2TableProducer
import LeanCompCert.Ports.Section413WindowEventScanner

/-!
# Executable Section 4.1.3 producer/scanner pipeline

This emits two constant-size rolled pipelines.  Each first constructs its
G-table in compiled code and then invokes the compiled event scanner on the
same caller-owned array.  The driver succeeds only when both producer and
scanner failure registers remain zero.
-/

namespace LeanCompCert.Testing.Section413WindowPipelineCertificate

open LeanCompCert.Verified.ArrayState

def g1TableCfg : LeanCompCert.Ports.Section413G1Program.Cfg :=
  ⟨99999, 999, 33⟩

def g2TableCfg : LeanCompCert.Ports.Section413G2Program.Cfg :=
  ⟨99999, 999, 33⟩

def g1Producer : AProgram :=
  LeanCompCert.Ports.Section413G1TableProducer.producerProgram g1TableCfg

def g2Producer : AProgram :=
  LeanCompCert.Ports.Section413G2TableProducer.producerProgram g2TableCfg

def g1Scanner : AProgram :=
  LeanCompCert.Ports.Section413WindowEventScanner.program
    LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg

def g2Scanner : AProgram :=
  LeanCompCert.Ports.Section413WindowEventScanner.program
    LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg

def mainC : String :=
  "\nstatic uint64_t g1_cells[500000];\n" ++
  "static uint64_t g2_cells[500000];\n" ++
  "int main(void)\n{\n" ++
  "    uint64_t g1p = l_Section413_G1_producer(g1_cells);\n" ++
  "    uint64_t g1s = l_Section413_G1_scanner(g1_cells);\n" ++
  "    uint64_t g2p = l_Section413_G2_producer(g2_cells);\n" ++
  "    uint64_t g2s = l_Section413_G2_scanner(g2_cells);\n" ++
  "    return (g1p == 0 && g1s == 0 && g2p == 0 && g2s == 0) ? 0 : 1;\n" ++
  "}\n"

def emittedC : Except (Array String) String := do
  let g1p ← g1Producer.emitRolled "Section413.G1.producer"
  let g1s ← g1Scanner.emitRolled "Section413.G1.scanner"
  let g2p ← g2Producer.emitRolled "Section413.G2.producer"
  let g2s ← g2Scanner.emitRolled "Section413.G2.scanner"
  pure (g1p ++ "\n" ++ g1s ++ "\n" ++ g2p ++ "\n" ++ g2s ++ mainC)

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      match emittedC with
      | .ok source => IO.FS.writeFile path source; pure 0
      | .error errors =>
          for error in errors do IO.eprintln error
          pure 1
  | _ =>
      IO.eprintln "usage: Section413WindowPipelineCertificate <output.c>"
      pure 2

end LeanCompCert.Testing.Section413WindowPipelineCertificate

def main (args : List String) : IO UInt32 :=
  LeanCompCert.Testing.Section413WindowPipelineCertificate.main args

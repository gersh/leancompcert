import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585B

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585A.state00

def state10 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585B.state10

def words : List Nat :=
  LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585B.words

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58500 100 state00 =
      (state10, words) := by
  simpa [state00, state10, words] using
    LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585B.segment

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585

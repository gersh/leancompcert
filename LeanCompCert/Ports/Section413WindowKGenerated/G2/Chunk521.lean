import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521B

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521A.state00

def state10 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521B.state10

def words : List Nat :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521B.words

theorem segment :
    trace directG2 2 16 37273 0 52100 100 state00 =
      (state10, words) := by
  simpa [state00, state10, words] using
    LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521B.segment

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521

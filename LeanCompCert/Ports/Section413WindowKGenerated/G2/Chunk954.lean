import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954B

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954A.state00

def state10 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954B.state10

def words : List Nat :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954B.words

theorem segment :
    trace directG2 2 16 37273 0 95400 100 state00 =
      (state10, words) := by
  simpa [state00, state10, words] using
    LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954B.segment

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk954

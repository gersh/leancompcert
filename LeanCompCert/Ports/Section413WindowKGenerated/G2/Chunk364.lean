import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364B

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364A.state00

def state10 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364B.state10

def words : List Nat :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364B.words

theorem segment :
    trace directG2 2 16 37273 0 36400 100 state00 =
      (state10, words) := by
  simpa [state00, state10, words] using
    LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364B.segment

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999B

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999A.state00

def state10 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999B.state10

def words : List Nat :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999B.words

theorem segment :
    trace directG2 2 16 37273 0 99900 99 state00 =
      (state10, words) := by
  simpa [state00, state10, words] using
    LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999B.segment

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk999

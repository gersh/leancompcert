import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879B

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879A.state00

def state10 : KState :=
  LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879B.state10

def words : List Nat :=
  LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879B.words

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87900 100 state00 =
      (state10, words) := by
  simpa [state00, state10, words] using
    LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879B.segment

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk879

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk750A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk750B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk750A

def state06 : KState := ⟨⟨360568280318986290, 360568316832335426⟩, ⟨1048024485631858890, 1049875613935242440⟩, true⟩

def words05 : List Nat := [360582304847792565, 360582304756405609, 360582304664821516, 360582304671225278, 360582304672122165, 360582304638548243, 360582304604858950, 360582304475836051, 360582304169250358, 360582303984133125]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566034042953469, 360566070566378423⟩, ⟨1216599099647575527, 1218450984293373061⟩, true⟩

def words06 : List Nat := [360582303798668576, 360582303609243807, 360582303367173724, 360582303024343373, 360582302681340802, 360582302293729952, 360582301995116601, 360582301843284501, 360582301691332169, 360582301430695639]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588329114407911, 360588365647923349⟩, ⟨(-457272691357783470), (-455420049171272836)⟩, true⟩

def words07 : List Nat := [360582301215353436, 360582301105799174, 360582300995929894, 360582300988709898, 360582300804164969, 360582300442024586, 360582300079689282, 360582299864418794, 360582299849678174, 360582299931574722]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589914229770440, 360589950773481667⟩, ⟨(-576304497372973453), (-574451089636738393)⟩, true⟩

def words08 : List Nat := [360582299932528137, 360582299923877175, 360582300120349621, 360582300317130452, 360582300468785631, 360582300594958850, 360582300623551048, 360582300652256330, 360582300653138238, 360582300707699660]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554485628652323, 360554522182425929⟩, ⟨2084278934842709985, 2086133098214727857⟩, true⟩

def words09 : List Nat := [360582300935488235, 360582301163475251, 360582301302589371, 360582301303658521, 360582301265520136, 360582301135375115, 360582301004894101, 360582300901971658, 360582300621752624, 360582300252974727]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk750B

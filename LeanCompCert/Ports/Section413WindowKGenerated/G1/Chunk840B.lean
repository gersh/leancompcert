import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk840A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk840B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk840A

def state06 : KState := ⟨⟨362483082707850180, 362483189069096019⟩, ⟨173268438889932055, 179305426973296595⟩, true⟩

def words05 : List Nat := [371285322941381222, 371285322773954739, 371285322605371201, 371285322579506695, 371285322481779239, 371285322428502169, 371285322374152072, 371285322320512916, 371285322155655520, 371285322133894655]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481774526922556, 362481880914177865⟩, ⟨283257199456039933, 289296374032067423⟩, true⟩

def words06 : List Nat := [371285322226575776, 371285322229512897, 371285322220917788, 371285322185921602, 371285322149774533, 371285322102200749, 371285322002692045, 371285322025808826, 371285322047943529, 371285322051016596]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485872696939772, 362485979110581959⟩, ⟨(-61318003019584817), (-55276609966271361)⟩, true⟩

def words07 : List Nat := [371285322027734386, 371285322046914075, 371285322137195891, 371285322140113820, 371285322056566616, 371285321948046037, 371285321838401315, 371285321788493958, 371285321678506138, 371285321689643028]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479484825838556, 362479591265804640⟩, ⟨475771079396928347, 481814685894791587⟩, true⟩

def words08 : List Nat := [371285321699586069, 371285321702512013, 371285321567677930, 371285321554641609, 371285321555053141, 371285321557971210, 371285321386648635, 371285321216305619, 371285321044748102, 371285321015904472]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465966205940329, 362466072672205108⟩, ⟨1612640465867729501, 1618686283954565683⟩, true⟩

def words09 : List Nat := [371285320949781599, 371285320919717850, 371285320888695601, 371285320858364544, 371285320680733863, 371285320508643207, 371285320334975349, 371285320256211352, 371285320059331473, 371285319833726566]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk840B

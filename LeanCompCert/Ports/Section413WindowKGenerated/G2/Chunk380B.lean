import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk380A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk380B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk380A

def state06 : KState := ⟨⟨360652068447728127, 360652077334300621⟩, ⟨(-2672884755621612059), (-2672656135667488995)⟩, true⟩

def words05 : List Nat := [360581841657757934, 360581843285175332, 360581845601644287, 360581847470296460, 360581848696432735, 360581849922544744, 360581851443711655, 360581853309178505, 360581855154688465, 360581857000214090]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360643121510251411, 360643130401717327⟩, ⟨(-2332626235552628087), (-2332397429331275609)⟩, true⟩

def words06 : List Nat := [360581858500304108, 360581859314220000, 360581860355375332, 360581861396627994, 360581862049372342, 360581862719189519, 360581863043214402, 360581863367278861, 360581864379866506, 360581865989715245]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360555690004339126, 360555698900651369⟩, ⟨996388315689997248, 996617306435140798⟩, true⟩

def words07 : List Nat := [360581867699256492, 360581869408803520, 360581870528468559, 360581870962398811, 360581871214760180, 360581871467244900, 360581871602018188, 360581871602532212, 360581871260371402, 360581870573614477]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360610297934907996, 360610306836068823⟩, ⟨(-1083272959211481433), (-1083043783807981757)⟩, true⟩

def words08 : List Nat := [360581869886766840, 360581870112280678, 360581871181175423, 360581872250112439, 360581872730063652, 360581872730577763, 360581872719936823, 360581872689989923, 360581873026560594, 360581873773565661]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590216347672572, 360590225253726955⟩, ⟨(-318267093275427212), (-318037731452388898)⟩, true⟩

def words09 : List Nat := [360581874175158468, 360581874576786529, 360581875078566443, 360581876119077299, 360581876830818127, 360581877542604643, 360581877775141289, 360581877775655750, 360581877806120443, 360581878025794555]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk380B

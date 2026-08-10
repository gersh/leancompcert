import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk929A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk929B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk929A

def state06 : KState := ⟨⟨360601097104170281, 360601154049947084⟩, ⟨(-1782453249532548185), (-1778878613497570293)⟩, true⟩

def words05 : List Nat := [360582017632692912, 360582017773879962, 360582017905808593, 360582017922548271, 360582017923788645, 360582017841961586, 360582017792346971, 360582017884043121, 360582018090984054, 360582018298250162]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593059103179532, 360593116061773468⟩, ⟨(-1035303908906799952), (-1031728081329395916)⟩, true⟩

def words06 : List Nat := [360582018417553633, 360582018458379700, 360582018533506518, 360582018609021975, 360582018655236640, 360582018702820507, 360582018704042379, 360582018656421084, 360582018630071402, 360582018750984842]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588270798408013, 360588327769667558⟩, ⟨(-590051673660600748), (-586474668497477956)⟩, true⟩

def words07 : List Nat := [360582018967477993, 360582019184233499, 360582019320586861, 360582019498669610, 360582019646720032, 360582019795129883, 360582020036891858, 360582020163536335, 360582020232584381, 360582020301813938]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591314982428561, 360591371966411656⟩, ⟨(-873158608746801143), (-869580420487384133)⟩, true⟩

def words08 : List Nat := [360582020336051036, 360582020428358070, 360582020509710889, 360582020591312611, 360582020592553444, 360582020575690511, 360582020553749270, 360582020601544077, 360582020632393260, 360582020734351700]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589409669684652, 360589466666466259⟩, ⟨(-695962572152968758), (-692383193696036396)⟩, true⟩

def words09 : List Nat := [360582020769048724, 360582020803891865, 360582020954037013, 360582021194160756, 360582021353844132, 360582021513724272, 360582021616061821, 360582021617407519, 360582021684350657, 360582021765941577]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk929B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk889A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk889B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk889A

def state06 : KState := ⟨⟨360576519880684632, 360576571853137439⟩, ⟨487263412215294283, 490385595770583363⟩, true⟩

def words05 : List Nat := [360582083628648406, 360582083874941620, 360582084052219150, 360582084138563140, 360582084192911876, 360582084247637673, 360582084321308745, 360582084340637690, 360582084341785721, 360582084281147451]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590962223409736, 360591014207981899⟩, ⟨(-797670981200759592), (-794547719448520908)⟩, true⟩

def words06 : List Nat := [360582084220222396, 360582084246667520, 360582084262206100, 360582084277973788, 360582084279168890, 360582084189632386, 360582083973710092, 360582083838990075, 360582083703886776, 360582083795606535]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585193049004950, 360585245045790778⟩, ⟨(-284337921824767272), (-281213573362602998)⟩, true⟩

def words07 : List Nat := [360582083824379897, 360582083853299718, 360582083987636954, 360582084186159935, 360582084352001751, 360582084518048240, 360582084577059151, 360582084594487940, 360582084631050563, 360582084668031902]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577288036146234, 360577340045006073⟩, ⟨419055520746921971, 422180943616525617⟩, true⟩

def words08 : List Nat := [360582084799276335, 360582084804670204, 360582084805823883, 360582084748549632, 360582084691050319, 360582084546200255, 360582084464292488, 360582084392034867, 360582084319638994, 360582084184163468]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594619108315873, 360594671129301997⟩, ⟨(-1123396849081753411), (-1120270347035419049)⟩, true⟩

def words09 : List Nat := [360582084131908267, 360582084077133874, 360582084091822328, 360582084093105299, 360582084038078225, 360582083858641437, 360582083678960017, 360582083678232530, 360582083820701897, 360582083963460766]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk889B

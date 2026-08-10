import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk741A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563717157356388, 360563752706562316⟩, ⟨1376580648804540735, 1378359870248322175⟩, true⟩

def state01 : KState := ⟨⟨360571960960930069, 360571996520070892⟩, ⟨765730771964982572, 767510729634738934⟩, true⟩

def words00 : List Nat := [360582353804164087, 360582353736022099, 360582353719596812, 360582353574834559, 360582353429904239, 360582353239376447, 360582353166403015, 360582353122008108, 360582353077515910, 360582352892080537]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580020054274383, 360580055623365074⟩, ⟨168400251126083533, 170180946229238747⟩, true⟩

def words01 : List Nat := [360582352753191863, 360582352719319710, 360582352704253554, 360582352705307598, 360582352543479933, 360582352220481012, 360582351897270742, 360582351716834456, 360582351672490528, 360582351642607239]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360553922413003309, 360553957992148934⟩, ⟨2102779790909472810, 2104561231333182004⟩, true⟩

def words02 : List Nat := [360582351612570656, 360582351479275675, 360582351163900204, 360582350844664385, 360582350525146949, 360582350152704243, 360582349726209226, 360582349209016884, 360582348691643224, 360582348134214673]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360526462628316067, 360526498217385445⟩, ⟨4138605807964183967, 4140387984086025315⟩, true⟩

def words03 : List Nat := [360582347752094542, 360582347551838828, 360582347351482037, 360582347059396547, 360582346637076883, 360582346169221670, 360582345701087291, 360582345141882882, 360582344504799891, 360582343752644227]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561925042799505, 360561960641808953⟩, ⟨1509255957857704116, 1511038870986197858⟩, true⟩

def words04 : List Nat := [360582343000262628, 360582342394911413, 360582341882421766, 360582341551758610, 360582341221004169, 360582340734971155, 360582340107584912, 360582339604306461, 360582339100731581, 360582338778976670]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk741A

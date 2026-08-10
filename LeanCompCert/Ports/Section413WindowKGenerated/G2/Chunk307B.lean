import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk307A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk307B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk307A

def state06 : KState := ⟨⟨360516389722178017, 360516395425268998⟩, ⟨2056347483280359253, 2056466118023940095⟩, true⟩

def words05 : List Nat := [360583269381070914, 360583268399443686, 360583267417840229, 360583265616351479, 360583262760952998, 360583259639879169, 360583256518886006, 360583254450846372, 360583252803760506, 360583250630666396]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558799100027221, 360558804806972990⟩, ⟨751648604127672522, 751767357464063426⟩, true⟩

def words06 : List Nat := [360583248457622143, 360583246749513044, 360583245569259391, 360583245441365510, 360583245313454590, 360583244209232051, 360583242051729719, 360583240058774145, 360583238065829045, 360583236635294865]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562772819198372, 360562778530046417⟩, ⟨629408942153914367, 629527815581985591⟩, true⟩

def words07 : List Nat := [360583235841675455, 360583234370694113, 360583232899723245, 360583232782835992, 360583232805824245, 360583232828877193, 360583232829241516, 360583232327277965, 360583231689702932, 360583231025679361]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360548649945713675, 360548655660412202⟩, ⟨1064186233010897190, 1064305224976247580⟩, true⟩

def words08 : List Nat := [360583230747983486, 360583230748392369, 360583230082758976, 360583228802198314, 360583227521652329, 360583225765610275, 360583224822629330, 360583224232502726, 360583223642375560, 360583222247777459]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360539009785485462, 360539015504051993⟩, ⟨1360978594711398188, 1361097705791381950⟩, true⟩

def words09 : List Nat := [360583221125488702, 360583220612959674, 360583220100350246, 360583219306968898, 360583217795845502, 360583215378352212, 360583212960939881, 360583210321799614, 360583208422407325, 360583206988006259]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk307B

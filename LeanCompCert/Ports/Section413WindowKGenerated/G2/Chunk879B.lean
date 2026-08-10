import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk879A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk879B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk879A

def state06 : KState := ⟨⟨360592419885317194, 360592470651452421⟩, ⟨(-909206890679563908), (-906191419147530432)⟩, true⟩

def words05 : List Nat := [360582168050686101, 360582168007136631, 360582168027965734, 360582168167645933, 360582168215800676, 360582168264150828, 360582168265291047, 360582168231187967, 360582168337374687, 360582168455943645]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599132285862611, 360599183063939810⟩, ⟨(-1499617392092141197), (-1496600870085327501)⟩, true⟩

def words06 : List Nat := [360582168703175364, 360582168986189090, 360582169200141119, 360582169414226521, 360582169578131919, 360582169808229018, 360582170054511846, 360582170301024949, 360582170434796585, 360582170629500219]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360615819956039470, 360615870746077964⟩, ⟨(-2967790975826649530), (-2964773401528727970)⟩, true⟩

def words07 : List Nat := [360582170817954444, 360582171006771533, 360582171324271941, 360582171512931999, 360582171567238883, 360582171621647900, 360582171804841719, 360582172095182708, 360582172479233327, 360582172863563231]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598518789937013, 360598569592062424⟩, ⟨(-1445638030716265947), (-1442619392952393549)⟩, true⟩

def words08 : List Nat := [360582173183038321, 360582173373589862, 360582173560853106, 360582173748486768, 360582173903311076, 360582174070031401, 360582174165996712, 360582174262098177, 360582174325300329, 360582174513100344]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574176136579600, 360574226950635168⟩, ⟨696463275668889983, 699482963228790827⟩, true⟩

def words09 : List Nat := [360582174829456970, 360582175146052907, 360582175396906122, 360582175518852878, 360582175608156958, 360582175697795297, 360582175732968205, 360582175734237630, 360582175709675891, 360582175620671859]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk879B

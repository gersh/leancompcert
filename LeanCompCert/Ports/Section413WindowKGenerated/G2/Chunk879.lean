import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk879

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603940797913301, 360603991492143377⟩, ⟨(-1921628432050918864), (-1918619283138432810)⟩, true⟩

def state01 : KState := ⟨⟨360595968477980714, 360596019184130808⟩, ⟨(-1220896543217343069), (-1217886346477159795)⟩, true⟩

def words00 : List Nat := [360582164677252490, 360582164780629746, 360582164819238858, 360582164857975441, 360582164864040051, 360582164980719710, 360582165140823497, 360582165301163583, 360582165396601296, 360582165555500977]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605332864077347, 360605383582195759⟩, ⟨(-2044192149605669631), (-2041180900671225257)⟩, true⟩

def words01 : List Nat := [360582165843339445, 360582166131568001, 360582166377014681, 360582166519383020, 360582166551755923, 360582166584227597, 360582166745674435, 360582166972494394, 360582167237587858, 360582167502980655]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581838671348709, 360581889401527301⟩, ⟨21439638823468853, 24451948149055763⟩, true⟩

def words02 : List Nat := [360582167703585952, 360582167775128523, 360582167866463606, 360582167958165457, 360582168015956109, 360582168017222318, 360582167945919062, 360582167772163663, 360582167598169843, 360582167485777831]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579331150557553, 360579381892657486⟩, ⟨242019237674324140, 245032595304031466⟩, true⟩

def words03 : List Nat := [360582167609647676, 360582167736928843, 360582167799334885, 360582167930920495, 360582168006965380, 360582168083344118, 360582168247627137, 360582168282993626, 360582168284133495, 360582168253759420]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585107956136192, 360585158710211136⟩, ⟨(-266046006128580646), (-263031595357936872)⟩, true⟩

def words04 : List Nat := [360582168223119396, 360582168137533313, 360582168223651319, 360582168332032137, 360582168333214296, 360582168310489920, 360582168158390812, 360582168085841281, 360582168014238086, 360582168049555113]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk879

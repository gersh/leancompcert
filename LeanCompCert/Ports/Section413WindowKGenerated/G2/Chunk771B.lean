import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk771A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk771B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk771A

def state06 : KState := ⟨⟨360581064753769994, 360581103422831919⟩, ⟨80175399816959651, 82190610492119099⟩, true⟩

def words05 : List Nat := [360582167849568547, 360582167805694863, 360582167884311148, 360582168167369810, 360582168357288975, 360582168547378370, 360582168652405195, 360582168653506016, 360582168632510679, 360582168619961159]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564617317672405, 360564655997118532⟩, ⟨1349270371993557157, 1351286383964914147⟩, true⟩

def words06 : List Nat := [360582168607061983, 360582168554782051, 360582168405015261, 360582168133767402, 360582167862354770, 360582167442379385, 360582167109483222, 360582166944454410, 360582166779286037, 360582166511359363]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594871552727978, 360594910242562288⟩, ⟨(-985622134972310394), (-983605321295877038)⟩, true⟩

def words07 : List Nat := [360582166285344192, 360582166227271561, 360582166242924509, 360582166244025953, 360582166208351225, 360582166013942035, 360582165819319732, 360582165772198300, 360582165938215173, 360582166104480431]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582484024902934, 360582522725237166⟩, ⟨(-29510392429884504), (-27492768318456648)⟩, true⟩

def words08 : List Nat := [360582166163001259, 360582166280683805, 360582166523609336, 360582166766863235, 360582166935950038, 360582166937859632, 360582166938847540, 360582166812277942, 360582166685514680, 360582166559773337]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575264046704599, 360575302757413498⟩, ⟨527893188735419911, 529911613719459619⟩, true⟩

def words09 : List Nat := [360582166732797076, 360582166906027320, 360582166992402897, 360582167028823291, 360582167029745111, 360582167024310932, 360582167018536936, 360582166989364541, 360582166985260872, 360582166897487585]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk771B

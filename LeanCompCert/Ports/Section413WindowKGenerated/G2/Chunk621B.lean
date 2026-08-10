import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk621A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk621B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk621A

def state06 : KState := ⟨⟨360591385674489087, 360591410342834429⟩, ⟨(-544883675218641063), (-543847811231940589)⟩, true⟩

def words05 : List Nat := [360582658955589039, 360582659385126218, 360582659709918254, 360582660165182206, 360582660513339844, 360582660861628439, 360582661079610053, 360582661080482110, 360582661181409864, 360582661323172070]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563621520796650, 360563646197350049⟩, ⟨1181048744258471742, 1182085118500014794⟩, true⟩

def words06 : List Nat := [360582661503459559, 360582661504331660, 360582661426974384, 360582661220402777, 360582661013695540, 360582660741224391, 360582660635615097, 360582660478927156, 360582660322150556, 360582659951869915]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604309135051754, 360604333819836588⟩, ⟨(-1348687026574202935), (-1347650140543290807)⟩, true⟩

def words07 : List Nat := [360582659646745152, 360582659600517913, 360582659698536283, 360582659850691275, 360582659851496496, 360582659781164876, 360582659825863777, 360582660099758236, 360582660449030997, 360582660798486927]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596227516984825, 360596252210094308⟩, ⟨(-846341013779498501), (-845303610081057719)⟩, true⟩

def words08 : List Nat := [360582660943732281, 360582660944604695, 360582660832196832, 360582660758959438, 360582660685493299, 360582660546297143, 360582660445119367, 360582660188828116, 360582659933642595, 360582660153203745]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360576343702703322, 360576368404023957⟩, ⟨390437909523402232, 391475823914884678⟩, true⟩

def words09 : List Nat := [360582660630892962, 360582661108739405, 360582661456447030, 360582661782182431, 360582661932111561, 360582662082254601, 360582662298276177, 360582662327059287, 360582662327843782, 360582662227559567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk621B

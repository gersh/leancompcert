import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk230

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574644832236507, 360574647940926372⟩, ⟨133656486396936330, 133704860484258870⟩, true⟩

def state01 : KState := ⟨⟨360530118692288165, 360530121803824260⟩, ⟨1157896693052983556, 1157945132616988466⟩, true⟩

def words00 : List Nat := [360580460943259231, 360580458850838644, 360580457898840070, 360580458365653134, 360580458365903152, 360580457972381931, 360580455701475817, 360580452482099961, 360580449262951765, 360580445364563808]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360525193906663111, 360525197021009045⟩, ⟨1271390617190191976, 1271439121423169894⟩, true⟩

def words01 : List Nat := [360580443177870490, 360580442875585140, 360580442573294058, 360580441320509832, 360580439082854487, 360580436362498366, 360580433642286057, 360580432805572094, 360580431354138709, 360580428955041329]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611771517764579, 360611774634934228⟩, ⟨(-722292487745745808), (-722243918497175008)⟩, true⟩

def words02 : List Nat := [360580426556085189, 360580426489514945, 360580426489763936, 360580425267771264, 360580424045861752, 360580421205301462, 360580417429723447, 360580415536218007, 360580413642789295, 360580414992778127]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589370491178619, 360589373611195430⟩, ⟨(-206267725990248052), (-206219091156979238)⟩, true⟩

def words03 : List Nat := [360580415380972544, 360580415769163128, 360580417259399265, 360580420223713190, 360580422037914180, 360580423852007001, 360580424232170064, 360580424232468969, 360580423129464944, 360580423518267303]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589774109325019, 360589777232156612⟩, ⟨(-215527442981790700), (-215478743281740790)⟩, true⟩

def words04 : List Nat := [360580425786873321, 360580427021861826, 360580427310409443, 360580427598969671, 360580427599221708, 360580426893801062, 360580427956586950, 360580429019337272, 360580429019607432, 360580429319125432]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360658013141367138, 360658016267026075⟩, ⟨(-1789162398338665420), (-1789113633454379642)⟩, true⟩

def words05 : List Nat := [360580429319371784, 360580429052591415, 360580430396812140, 360580430397111243, 360580430139070389, 360580428220448070, 360580426301933246, 360580427748609063, 360580431113487804, 360580434478142056]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613130325691052, 360613133454198731⟩, ⟨(-754034050372585448), (-753985219782025668)⟩, true⟩

def words06 : List Nat := [360580436898405283, 360580438793322397, 360580442564788863, 360580446336015731, 360580448832416840, 360580450570978598, 360580450857068030, 360580451143161102, 360580451143404447, 360580452373197387]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565582727190098, 360565585858520950⟩, ⟨343329342800179734, 343378238535646994⟩, true⟩

def words07 : List Nat := [360580455665819252, 360580458958217868, 360580461307599720, 360580462387619663, 360580462387871904, 360580462300326942, 360580463360101914, 360580464242554924, 360580464242826408, 360580463598492166]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360703150315026861, 360703153449184823⟩, ⟨(-2832323608833988836), (-2832274647834984284)⟩, true⟩

def words08 : List Nat := [360580464183767835, 360580466353468353, 360580469560550249, 360580472767411552, 360580474423889855, 360580477109550787, 360580481668100069, 360580486226343469, 360580491056157940, 360580496368597799]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360655779139400865, 360655782276415395⟩, ⟨(-1738371792269674953), (-1738322765298676097)⟩, true⟩

def words09 : List Nat := [360580500557635094, 360580504746342571, 360580508864256809, 360580513935684910, 360580518125422197, 360580522314845241, 360580525563265477, 360580526950254899, 360580530208303814, 360580533466177801]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk230

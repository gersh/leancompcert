import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk230A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk230A

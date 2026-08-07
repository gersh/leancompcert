import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk439

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469977616944118, 362470005171380619⟩, ⟨681004911110183249, 681822222309284485⟩, true⟩

def state01 : KState := ⟨⟨362473374241881648, 362473401809304493⟩, ⟨531906167910766319, 532724049276683157⟩, true⟩

def words00 : List Nat := [371285536076508736, 371285535871063351, 371285535416281040, 371285535387894282, 371285535359009167, 371285535252226229, 371285534586216984, 371285534261164069, 371285533988382957, 371285533989884696]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484481327452032, 362484508908140912⟩, ⟨44126178555421781, 44944642498429423⟩, true⟩

def words01 : List Nat := [371285533714711847, 371285533243930608, 371285532818698114, 371285532820304050, 371285532673511897, 371285532679324110, 371285532683788525, 371285532685264846, 371285532259355268, 371285532237888144]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362460339521844909, 362460367115447774⟩, ⟨1104576859821075907, 1105395891013296963⟩, true⟩

def words02 : List Nat := [371285532646487203, 371285532647938490, 371285532389261208, 371285532031960393, 371285531674152782, 371285531331356325, 371285530729794664, 371285530411668511, 371285530093058287, 371285529780847576]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495356249703493, 362495383856434663⟩, ⟨(-433820105612546914), (-433000497627229578)⟩, true⟩

def words03 : List Nat := [371285529209055787, 371285529099146352, 371285529394755632, 371285529396217149, 371285529340808175, 371285529168190045, 371285529260873600, 371285529271372501, 371285529496648575, 371285529722536317]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483296389667093, 362483324009483235⟩, ⟨96068273771963478, 96888456778522692⟩, true⟩

def words04 : List Nat := [371285529886295717, 371285529887747835, 371285529501582191, 371285529568615441, 371285529569645564, 371285529560319471, 371285529203447446, 371285528827591473, 371285528523338102, 371285528524995830]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470340478759158, 362470368111690514⟩, ⟨665631043850683331, 666451803335211979⟩, true⟩

def words05 : List Nat := [371285528943153752, 371285529412058444, 371285529785738946, 371285529787191335, 371285529471113251, 371285529225905688, 371285529210608959, 371285529212062585, 371285528868982782, 371285528525779123]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497555191466073, 362497582837394443⟩, ⟨(-530763150999537072), (-529941820099500406)⟩, true⟩

def words06 : List Nat := [371285528354312375, 371285528355916784, 371285528795920094, 371285529275581222, 371285529669126914, 371285529708535934, 371285529795119097, 371285529882447116, 371285530486104332, 371285530761705933]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507849510745007, 362507877169891611⟩, ⟨(-983396489950488608), (-982574577776383708)⟩, true⟩

def words07 : List Nat := [371285531036244367, 371285531311247114, 371285532102691003, 371285532707248469, 371285533471386984, 371285534236060098, 371285534980532208, 371285535263530300, 371285535772525480, 371285536282286137]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484835228355451, 362484862900455005⟩, ⟨28863445597760160, 29685927510508078⟩, true⟩

def words08 : List Nat := [371285536937635387, 371285536939088780, 371285536905642367, 371285536874881998, 371285536934554670, 371285536936155721, 371285537120972380, 371285537472872070, 371285537732491759, 371285537733996958]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362507413699004365, 362507441384266209⟩, ⟨(-964475856177198993), (-963652795192008009)⟩, true⟩

def words09 : List Nat := [371285538221017302, 371285538724144721, 371285539418072230, 371285539423901247, 371285539425046008, 371285539296350486, 371285539553416319, 371285539683954625, 371285540182708835, 371285540682118713]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk439

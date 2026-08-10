import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk528A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575880023157730, 360575897590236701⟩, ⟨322328643637576113, 322955359498784967⟩, true⟩

def state01 : KState := ⟨⟨360568399229548751, 360568416803526011⟩, ⟨717260698727952739, 717887778853603795⟩, true⟩

def words00 : List Nat := [360582014053776264, 360582013811484293, 360582013450957903, 360582012911141927, 360582012371226901, 360582011666810292, 360582011184991957, 360582011061217451, 360582010937354287, 360582010588393529]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577875381126526, 360577892962011864⟩, ⟨216757565613460904, 217385010588898680⟩, true⟩

def words01 : List Nat := [360582010331584958, 360582010129500793, 360582010082118808, 360582010082850873, 360582009880789075, 360582009341726934, 360582008802545056, 360582008621351248, 360582008620590655, 360582008543431571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580854362609175, 360580871950478487⟩, ⟨59362148925294960, 59989962828479944⟩, true⟩

def words02 : List Nat := [360582008466174320, 360582008209885955, 360582008322773864, 360582008511468573, 360582008607042351, 360582008607774745, 360582008462253645, 360582008137509229, 360582007812646991, 360582007478830342]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360548633958182860, 360548651552950526⟩, ⟨1761754665847658207, 1762382844224957297⟩, true⟩

def words03 : List Nat := [360582007603083393, 360582007748967388, 360582007749624196, 360582007624266502, 360582007141424674, 360582006568875467, 360582005996116710, 360582005780977706, 360582005378802067, 360582004748337070]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572319390143599, 360572336991833835⟩, ⟨510058629029719627, 510687173229873691⟩, true⟩

def words04 : List Nat := [360582004117730270, 360582003731202425, 360582003524805979, 360582003309457777, 360582003094058997, 360582002572682282, 360582001693997523, 360582001041652357, 360582000389109948, 360581999946861837]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk528A

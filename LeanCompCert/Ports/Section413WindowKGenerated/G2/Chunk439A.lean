import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk439A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557230707064552, 360557242668668779⟩, ⟨1139519985573239501, 1139874851460588065⟩, true⟩

def state01 : KState := ⟨⟨360567688998917625, 360567700966180783⟩, ⟨680310206510756400, 680665320853470146⟩, true⟩

def words00 : List Nat := [360583207336284296, 360583206568201754, 360583206070700612, 360583205900246652, 360583205729743172, 360583205121792279, 360583204244642671, 360583203534693032, 360583202824601102, 360583202339919191]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579405830359721, 360579417803347319⟩, ⟨165705195724754901, 166060561455566417⟩, true⟩

def words01 : List Nat := [360583201987451360, 360583201128011142, 360583200268491264, 360583199927150920, 360583199922037260, 360583199784448561, 360583199646800651, 360583199248563945, 360583198866922083, 360583198781522537]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360552887969236096, 360552899947870899⟩, ⟨1330441337472627726, 1330796951256864344⟩, true⟩

def words02 : List Nat := [360583199010581046, 360583199011180933, 360583198809560416, 360583198216274921, 360583197622927766, 360583196657505474, 360583195952725487, 360583195229656667, 360583194506557839, 360583193527457898]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595366226180274, 360595378210485557⟩, ⟨(-535790980483082358), (-535435117566627756)⟩, true⟩

def words03 : List Nat := [360583192838371179, 360583192550280886, 360583192490707948, 360583192648725822, 360583192649279533, 360583192330773724, 360583192044268453, 360583192335370608, 360583192613194073, 360583192891135369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594643952243809, 360594655942260494⟩, ⟨(-504251097948143353), (-503894984044878437)⟩, true⟩

def words04 : List Nat := [360583192891670044, 360583192842174378, 360583192511507982, 360583192605186342, 360583192605693572, 360583192216732298, 360583192001667156, 360583191464328691, 360583190926899835, 360583191015773159]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk439A

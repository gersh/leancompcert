import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk895A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569243705856612, 360569296335820064⟩, ⟨1138303593645360900, 1141484447024440782⟩, true⟩

def state01 : KState := ⟨⟨360565567656862886, 360565620299029940⟩, ⟨1467412555387299220, 1470594501047690784⟩, true⟩

def words00 : List Nat := [360582050210529919, 360582050272886880, 360582050354332666, 360582050436023014, 360582050437235037, 360582050404778387, 360582050247400982, 360582050074317251, 360582049900878536, 360582049686819547]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582307819306074, 360582360473763881⟩, ⟨(-31121506504622225), (-27938460637495509)⟩, true⟩

def words01 : List Nat := [360582049504423735, 360582049259542275, 360582049014418515, 360582048894344664, 360582048836711504, 360582048747802637, 360582048658730788, 360582048497084477, 360582048380460592, 360582048385419945]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594893080530142, 360594945747162505⟩, ⟨(-1157837544322943561), (-1154653408528773053)⟩, true⟩

def words02 : List Nat := [360582048514584386, 360582048602999516, 360582048604182261, 360582048587350184, 360582048570308957, 360582048548849380, 360582048701582080, 360582048854562799, 360582048913360490, 360582049058769337]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591098235015811, 360591150913833733⟩, ⟨(-818065538915493010), (-814880312088127016)⟩, true⟩

def words03 : List Nat := [360582049197596384, 360582049336809366, 360582049600236339, 360582049770768948, 360582049831168886, 360582049891667568, 360582049948955441, 360582050069212433, 360582050171900648, 360582050274885228]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580388068538185, 360580440759659424⟩, ⟨140880978715017659, 144067307241435991⟩, true⟩

def words04 : List Nat := [360582050315802577, 360582050317094146, 360582050246750019, 360582050261642211, 360582050262722932, 360582050245959603, 360582050104483928, 360582049887690727, 360582049670654502, 360582049551476749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk895A

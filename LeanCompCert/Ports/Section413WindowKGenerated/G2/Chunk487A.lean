import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk487A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360541324133864828, 360541338980469662⟩, ⟨1985311049137330651, 1985799619845405803⟩, true⟩

def state01 : KState := ⟨⟨360598002088276612, 360598016941209419⟩, ⟨(-775191802913662381), (-774702924002301493)⟩, true⟩

def words00 : List Nat := [360582114316628475, 360582113733338495, 360582113362357058, 360582113326774376, 360582113291142474, 360582112853284068, 360582112487889953, 360582112410012639, 360582112548726914, 360582112875926377]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557274038839688, 360557288898168830⟩, ⟨1208935326836786376, 1209424517345236848⟩, true⟩

def words01 : List Nat := [360582112934332384, 360582112992806538, 360582113041892427, 360582113365230928, 360582113583664186, 360582113802199410, 360582113806915850, 360582113807586811, 360582113391270123, 360582112882514997]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360558869462422506, 360558884328067883⟩, ⟨1131194427369813089, 1131683925637211537⟩, true⟩

def words02 : List Nat := [360582112373544515, 360582112179385105, 360582111852664033, 360582111288401682, 360582110724050498, 360582110047683157, 360582109582673027, 360582109108663657, 360582108634600759, 360582107884924793]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591841919854376, 360591856791830200⟩, ⟨(-475608998708454321), (-475119191927061785)⟩, true⟩

def words03 : List Nat := [360582107408901031, 360582107352713061, 360582107659008596, 360582108105901616, 360582108204908909, 360582108303956947, 360582108323903699, 360582108556283184, 360582108756832431, 360582108957523825]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360553699899710527, 360553714778087600⟩, ⟨1383450918955158760, 1383941037764400980⟩, true⟩

def words04 : List Nat := [360582108958136196, 360582108767630319, 360582108156439754, 360582107855812025, 360582107555012089, 360582107149725086, 360582106323851842, 360582105288852536, 360582104253756265, 360582103312195588]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk487A

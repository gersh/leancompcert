import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk937A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568989306849383, 360569047198670811⟩, ⟨1216901499962960682, 1220564430742219886⟩, true⟩

def state01 : KState := ⟨⟨360585617470607551, 360585675375256395⟩, ⟨(-341146901679820109), (-337482768909786415)⟩, true⟩

def words00 : List Nat := [360582073362035938, 360582073414075143, 360582073604700361, 360582073795592186, 360582073889618972, 360582073890975559, 360582073939996126, 360582074010250495, 360582074021073027, 360582074060907922]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585875086589647, 360585933004151361⟩, ⟨(-365300809835680651), (-361635466936710147)⟩, true⟩

def words01 : List Nat := [360582074062116432, 360582074044751052, 360582074077849373, 360582074186875048, 360582074266860471, 360582074347089336, 360582074351823994, 360582074353181179, 360582074322834677, 360582074365565167]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575123492560387, 360575181422916371⟩, ⟨642299372358771712, 645965914399071078⟩, true⟩

def words02 : List Nat := [360582074398330879, 360582074399687692, 360582074319035300, 360582074150944741, 360582073982639334, 360582073748828701, 360582073588550979, 360582073478344061, 360582073367990117, 360582073196248272]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582322080479306, 360582380023627582⟩, ⟨(-32515249245244641), (-28847508118501529)⟩, true⟩

def words03 : List Nat := [360582073123825356, 360582073068953412, 360582073037416651, 360582073038773670, 360582072950249616, 360582072764330643, 360582072578174923, 360582072388722780, 360582072282643261, 360582072287331634]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583727185377500, 360583785141452245⟩, ⟨(-164323804095759388), (-160654851178183160)⟩, true⟩

def words04 : List Nat := [360582072288540461, 360582072236075897, 360582072165411735, 360582072129067101, 360582072092320336, 360582072027161373, 360582071911674287, 360582071739244051, 360582071566555308, 360582071507985102]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk937A

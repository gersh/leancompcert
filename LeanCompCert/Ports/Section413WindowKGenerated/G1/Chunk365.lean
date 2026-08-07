import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk365

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362508089671598735, 362508108435255494⟩, ⟨(-846550145375111833), (-846087299790678399)⟩, true⟩

def state01 : KState := ⟨⟨362463779617299023, 362463798391670636⟩, ⟨770936903892377471, 771400140623790651⟩, true⟩

def words00 : List Nat := [371284929176131960, 371284929177320906, 371284929006218739, 371284929256570178, 371284929508473385, 371284929509662386, 371284928762159004, 371284928000150523, 371284927237717220, 371284926853479012]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362437441519653998, 362437460304763240⟩, ⟨1732790081101774091, 1733253709917019461⟩, true⟩

def words01 : List Nat := [371284926275599398, 371284926253227596, 371284926230425333, 371284926210601592, 371284925191462579, 371284924352632690, 371284923513247318, 371284923089400284, 371284922000330485, 371284920702077507]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489290565865035, 362489309361615283⟩, ⟨(-160976382917903970), (-160512365437654836)⟩, true⟩

def words02 : List Nat := [371284919403347917, 371284918715120931, 371284917651199788, 371284917336406042, 371284917021269539, 371284916589592246, 371284915536902331, 371284915233396741, 371284915372821703, 371284915494339883]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465979391518226, 362465998198114322⟩, ⟨690683077193820553, 691147490926930505⟩, true⟩

def words03 : List Nat := [371284915495245102, 371284915412300456, 371284915362491028, 371284915363801478, 371284915025297685, 371284914914650661, 371284914803599969, 371284914667554527, 371284913533404013, 371284913017242044]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362457503860271272, 362457522677462259⟩, ⟨1000520105256484105, 1000984906182136809⟩, true⟩

def words04 : List Nat := [371284912730777770, 371284912731976000, 371284912318046224, 371284911885722181, 371284911452950021, 371284911248103570, 371284910670220758, 371284910248893463, 371284909827207736, 371284909405401579]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362510412046015422, 362510430873977412⟩, ⟨(-933542374880324159), (-933077180219934981)⟩, true⟩

def words05 : List Nat := [371284908656935193, 371284908656781309, 371284909031734503, 371284909032945770, 371284908797801319, 371284908448028907, 371284908416893416, 371284908418217924, 371284909067914301, 371284909767327706]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474151568595046, 362474170407308343⟩, ⟨392283361014683797, 392748948797914869⟩, true⟩

def words06 : List Nat := [371284910323907572, 371284910325098298, 371284910368628789, 371284910765017308, 371284911315980246, 371284911317171483, 371284911016503474, 371284910607054254, 371284910197115563, 371284910055894559]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362448768332328041, 362448787181748001⟩, ⟨1320811778517080567, 1321277757896691691⟩, true⟩

def words07 : List Nat := [371284910216452401, 371284910671124719, 371284911116081488, 371284911117272837, 371284910566229174, 371284909936064708, 371284909344901198, 371284909346092604, 371284908390893306, 371284907404763220]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486121898103651, 362486140758199317⟩, ⟨(-45627099343403238), (-45160729391093886)⟩, true⟩

def words08 : List Nat := [371284906418168050, 371284906084757357, 371284905802112978, 371284906034973070, 371284906153713544, 371284906154913470, 371284905809355686, 371284906010818159, 371284906520032307, 371284906554996587]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485540655445816, 362485559526414611⟩, ⟨(-24355415834135426), (-23888647979236994)⟩, true⟩

def words09 : List Nat := [371284906587352824, 371284906620124771, 371284906973726157, 371284907056373481, 371284907259754954, 371284907463588627, 371284907538086518, 371284907539279885, 371284906829626652, 371284906848947350]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk365

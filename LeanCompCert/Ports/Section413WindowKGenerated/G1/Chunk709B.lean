import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk709A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk709B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk709A

def state06 : KState := ⟨⟨362477877822671677, 362477952630110558⟩, ⟨515696796901176900, 519281796847964524⟩, true⟩

def words05 : List Nat := [371285270652335297, 371285270766975823, 371285270862317374, 371285270864760011, 371285270770083338, 371285270700410235, 371285270755160731, 371285270757598512, 371285270681389378, 371285270581024425]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491309715246852, 362491384544429427⟩, ⟨(-437493558981640422), (-433907015989831050)⟩, true⟩

def words06 : List Nat := [371285270479558550, 371285270481895007, 371285270433626416, 371285270486029455, 371285270521317531, 371285270523792865, 371285270419208126, 371285270412186135, 371285270592129847, 371285270680795129]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486889206329464, 362486964057693349⟩, ⟨(-123759139339657521), (-120171022030562351)⟩, true⟩

def words07 : List Nat := [371285270746947314, 371285270813913665, 371285270962948895, 371285271013911846, 371285271072905276, 371285271132856657, 371285271174495548, 371285271176931064, 371285271028126907, 371285271055030235]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474969746200824, 362475044619185523⟩, ⟨722369187848028716, 725958839917239548⟩, true⟩

def words08 : List Nat := [371285271278679719, 371285271281111782, 371285271240613672, 371285271160650464, 371285271079730708, 371285271060102844, 371285270940209044, 371285270904279144, 371285270867551179, 371285270831890373]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362507067052329450, 362507141947337575⟩, ⟨(-1556381446533871761), (-1552790230914610965)⟩, true⟩

def words09 : List Nat := [371285270743526258, 371285270800541917, 371285270954264998, 371285270999595091, 371285271012638154, 371285271026416158, 371285271237284427, 371285271349949210, 371285271659636077, 371285271970422960]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk709B

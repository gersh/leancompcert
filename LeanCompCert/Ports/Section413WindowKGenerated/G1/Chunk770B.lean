import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk770A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk770B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk770A

def state06 : KState := ⟨⟨362499965165303801, 362500053953827071⟩, ⟨(-1149390488310949052), (-1144770119088577626)⟩, true⟩

def words05 : List Nat := [371285197760645503, 371285197855966082, 371285198074163679, 371285198090229018, 371285198092298685, 371285198061876140, 371285198149824594, 371285198187647653, 371285198382231271, 371285198577967836]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492036632299267, 362492125444824218⟩, ⟨(-538453515741794242), (-533831296829174248)⟩, true⟩

def words06 : List Nat := [371285198751429506, 371285198754087188, 371285198751576458, 371285198777832498, 371285198854194312, 371285198856871754, 371285198817930572, 371285198778737655, 371285198864643700, 371285198957600371]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476457388411318, 362476546224874570⟩, ⟨662376892584903901, 667000956544932153⟩, true⟩

def words07 : List Nat := [371285199179549722, 371285199402609004, 371285199614249251, 371285199622022118, 371285199680142778, 371285199739574604, 371285199801445662, 371285199804110663, 371285199693709741, 371285199584456108]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491637804213135, 362491726664475165⟩, ⟨(-507775466452769064), (-503149567963864414)⟩, true⟩

def words08 : List Nat := [371285199529895672, 371285199532827054, 371285199636018628, 371285199751844239, 371285199834758489, 371285199837416515, 371285199705882803, 371285199719117559, 371285199880442095, 371285199967870324]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490090226006591, 362490179110471113⟩, ⟨(-388442034580886186), (-383814270196418448)⟩, true⟩

def words09 : List Nat := [371285200021177296, 371285200075322068, 371285200296503025, 371285200435360614, 371285200586539718, 371285200738756132, 371285200891502084, 371285200905019784, 371285200971403916, 371285201039237324]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk770B

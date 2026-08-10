import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk735A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk735B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk735A

def state06 : KState := ⟨⟨362480864518531704, 362480945134299551⟩, ⟨316625242329901927, 320630001777549951⟩, true⟩

def words05 : List Nat := [371285303798372149, 371285303729937318, 371285303773865032, 371285303835219615, 371285303939985674, 371285304045743178, 371285304117407725, 371285304119935547, 371285303945182353, 371285303889081737]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475946984451758, 362476027622774683⟩, ⟨678397664006269581, 682404082720415407⟩, true⟩

def words06 : List Nat := [371285303956883187, 371285303959411073, 371285303840484277, 371285303703004492, 371285303564582031, 371285303483353403, 371285303321630253, 371285303282784837, 371285303243025982, 371285303198182056]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479739785918277, 362479820447043337⟩, ⟨399374770693693001, 403382867079253517⟩, true⟩

def words07 : List Nat := [371285303132280583, 371285303193737557, 371285303340032326, 371285303342560720, 371285303243004540, 371285303120250763, 371285302996473608, 371285302922000443, 371285302753935602, 371285302682257788]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472382189908513, 362472462873849478⟩, ⟨940729413801079561, 944739189094450413⟩, true⟩

def words08 : List Nat := [371285302609641657, 371285302538183265, 371285302219860548, 371285302087449427, 371285301953674137, 371285301876812649, 371285301553292407, 371285301223782822, 371285300893275725, 371285300748412523]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465056853912240, 362465137560663053⟩, ⟨1479845413107162360, 1483856867092284666⟩, true⟩

def words09 : List Nat := [371285300575708758, 371285300481357914, 371285300386165938, 371285300264105529, 371285299933103765, 371285299628821904, 371285299323264332, 371285299202989306, 371285298930445771, 371285298659400720]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk735B

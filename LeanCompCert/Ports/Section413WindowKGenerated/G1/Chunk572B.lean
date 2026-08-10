import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk572A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk572B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk572A

def state06 : KState := ⟨⟨362498424968653560, 362498472863159282⟩, ⟨(-774488895421105250), (-772636340166891274)⟩, true⟩

def words05 : List Nat := [371284978985425670, 371284979199528581, 371284979537921976, 371284979539852932, 371284979471707246, 371284979303144272, 371284979217107477, 371284979219255140, 371284979386640961, 371284979624477337]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492032485981538, 362492080397899612⟩, ⟨(-408495541110483698), (-406641988735873678)⟩, true⟩

def words06 : List Nat := [371284979860346146, 371284979862277382, 371284979791745059, 371284979894394515, 371284980051616301, 371284980053564975, 371284980008286785, 371284979891217469, 371284979959361295, 371284980085547185]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483833432362889, 362483881361695484⟩, ⟨61199276624950895, 63053826416354075⟩, true⟩

def words07 : List Nat := [371284980515942648, 371284980947125419, 371284981345091311, 371284981491010942, 371284981690578016, 371284981891092044, 371284982179352622, 371284982181293824, 371284982178757864, 371284982161737669]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496460560564106, 362496508507208578⟩, ⟨(-662137778037194600), (-660282236535879336)⟩, true⟩

def words08 : List Nat := [371284982236307855, 371284982238436817, 371284982426535285, 371284982674517947, 371284982880977638, 371284982882909849, 371284982786560124, 371284982892614503, 371284983243612314, 371284983446788340]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482978546012264, 362483026510226743⟩, ⟨110358716187204163, 112215264365137235⟩, true⟩

def words09 : List Nat := [371284983655215496, 371284983864262736, 371284984224514900, 371284984434941116, 371284984663290904, 371284984892373771, 371284985110150306, 371284985112082885, 371284984923608180, 371284984891803797]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk572B

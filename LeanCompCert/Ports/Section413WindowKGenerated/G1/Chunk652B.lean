import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk652A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk652B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk652A

def state06 : KState := ⟨⟨362477659009956474, 362477721869045954⟩, ⟨505889570844908227, 508660257216403609⟩, true⟩

def words05 : List Nat := [371285516522386435, 371285516556709744, 371285516590184321, 371285516592446101, 371285516459472119, 371285516385284127, 371285516467654022, 371285516469876907, 371285516350954879, 371285516234004833]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480189489378811, 362480252368388324⟩, ⟨340718126056061247, 343490112508174493⟩, true⟩

def words06 : List Nat := [371285516116105146, 371285516096678631, 371285515971662533, 371285515898240001, 371285515824102448, 371285515716323522, 371285515295118922, 371285515109644189, 371285514969311867, 371285514971613515]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479406038330283, 362479468937610835⟩, ⟨391883259304284669, 394656568944754727⟩, true⟩

def words07 : List Nat := [371285514892648462, 371285514814393805, 371285514809851797, 371285514821811936, 371285514843280538, 371285514865550609, 371285514886864548, 371285514889088213, 371285514624377830, 371285514534561582]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477222043167466, 362477284962276279⟩, ⟨534512964094139716, 537287568226066440⟩, true⟩

def words08 : List Nat := [371285514550477480, 371285514552739866, 371285514466431644, 371285514374685479, 371285514282116311, 371285514200561997, 371285514108935685, 371285514181991279, 371285514207458260, 371285514209760214]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491216794105905, 362491279733294307⟩, ⟨(-379238634720404714), (-376462719489524510)⟩, true⟩

def words09 : List Nat := [371285514170270973, 371285514257946600, 371285514578837064, 371285514587979937, 371285514589717044, 371285514560095971, 371285514579653339, 371285514582104075, 371285514604941453, 371285514695706988]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk652B

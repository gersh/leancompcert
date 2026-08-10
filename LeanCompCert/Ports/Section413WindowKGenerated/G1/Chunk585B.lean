import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585A

def state06 : KState := ⟨⟨362491430442769166, 362491480626361836⟩, ⟨(-380835358971842485), (-378850236464329111)⟩, true⟩

def words05 : List Nat := [371285010453277278, 371285010552778805, 371285010800324217, 371285010903078900, 371285011009558935, 371285011116749862, 371285011206697505, 371285011208682906, 371285011186783856, 371285011299737217]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490741914379277, 362490792115604465⟩, ⟨(-340446226204434384), (-338460071044206342)⟩, true⟩

def words06 : List Nat := [371285011671420019, 371285011848675900, 371285012021604051, 371285012195174995, 371285012373188399, 371285012421476470, 371285012760733990, 371285013100801848, 371285013386033214, 371285013486743012]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362516456915173187, 362516507134267990⟩, ⟨(-1846713000055774124), (-1844725798181812452)⟩, true⟩

def words07 : List Nat := [371285013813634363, 371285014141538929, 371285014760169415, 371285014990770695, 371285015133950000, 371285015277791297, 371285015634949749, 371285015883033995, 371285016421953285, 371285016961717474]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502755863333163, 362502806100315330⟩, ⟨(-1044096560507558303), (-1042108310701817241)⟩, true⟩

def words08 : List Nat := [371285017481217403, 371285017704842170, 371285018047359458, 371285018390884098, 371285018820912275, 371285018991471240, 371285019136615248, 371285019282404161, 371285019644491416, 371285019950382716]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475626310994950, 362475676565798514⟩, ⟨545647270940222564, 547636564993724390⟩, true⟩

def words09 : List Nat := [371285020447719167, 371285020945864758, 371285021442417103, 371285021551096741, 371285021746730050, 371285021943318229, 371285022173771257, 371285022175750945, 371285022056907822, 371285021899672128]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk585B

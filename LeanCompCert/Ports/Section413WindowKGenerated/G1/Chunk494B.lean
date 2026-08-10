import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk494A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk494B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk494A

def state06 : KState := ⟨⟨362501846222962842, 362501881539835086⟩, ⟨(-837424677442314357), (-836244552310586785)⟩, true⟩

def words05 : List Nat := [371284973253094507, 371284973458449930, 371284973924829217, 371284973926478482, 371284973903324593, 371284973766194755, 371284973767199171, 371284973769016071, 371284974046039177, 371284974389710532]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478618120287984, 362478653452054412⟩, ⟨311579594140717610, 312760456014602734⟩, true⟩

def words06 : List Nat := [371284974733877363, 371284974737871529, 371284975149045634, 371284975561091266, 371284976045964862, 371284976047614263, 371284975988493247, 371284975849825415, 371284975710528014, 371284975676756547]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486214960357436, 362486250307002256⟩, ⟨(-64237759102687160), (-63056161120739628)⟩, true⟩

def words07 : List Nat := [371284975765786438, 371284975983297537, 371284976163034417, 371284976164685769, 371284975901042390, 371284975757485394, 371284975875070695, 371284975901403775, 371284975928393603, 371284975956016611]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485440539686171, 362485475901115406⟩, ⟨(-25834929524578209), (-24652599933697593)⟩, true⟩

def words08 : List Nat := [371284976390371609, 371284976622643184, 371284977025784498, 371284977429545900, 371284977761956047, 371284977763606621, 371284977606742697, 371284977594471353, 371284977766421856, 371284977778225715]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486951524615209, 362486986901069948⟩, ⟨(-100591232716768139), (-99408159439786987)⟩, true⟩

def words09 : List Nat := [371284977779478901, 371284977777458077, 371284978109092187, 371284978278136374, 371284978538094496, 371284978798687999, 371284978976677216, 371284978978328058, 371284978653364587, 371284978695994500]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk494B

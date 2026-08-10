import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk989A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk989B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk989A

def state06 : KState := ⟨⟨362490208140777834, 362490357416572705⟩, ⟨(-505269616366751253), (-495296177721132179)⟩, true⟩

def words05 : List Nat := [371285351980523143, 371285352041298877, 371285352202322731, 371285352228337486, 371285352237750316, 371285352248230910, 371285352321735773, 371285352345720929, 371285352398696452, 371285352453226325]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481072183956885, 362481221491087439⟩, ⟨398855808214736552, 408832348004779206⟩, true⟩

def words06 : List Nat := [371285352506246303, 371285352509723399, 371285352442867383, 371285352463498617, 371285352513178809, 371285352516716764, 371285352481742026, 371285352428690859, 371285352374207516, 371285352362543485]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478288798073490, 362478438136531014⟩, ⟨674367288839906250, 684346929217459874⟩, true⟩

def words07 : List Nat := [371285352356444010, 371285352393462401, 371285352409307969, 371285352412797051, 371285352343869868, 371285352292130005, 371285352258062602, 371285352261564153, 371285352194450754, 371285352128541698]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483345737984020, 362483495107534790⟩, ⟨173857652835870657, 183840370981178665⟩, true⟩

def words08 : List Nat := [371285352093305996, 371285352097198641, 371285352176198064, 371285352257136670, 371285352321265572, 371285352324744716, 371285352269375080, 371285352252426251, 371285352264962397, 371285352268571069]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487123214556928, 362487272615873875⟩, ⟨(-200084992195597205), (-190099129364293171)⟩, true⟩

def words09 : List Nat := [371285352252440853, 371285352225513206, 371285352268452482, 371285352306623281, 371285352362542858, 371285352419751765, 371285352475677461, 371285352479155850, 371285352418229633, 371285352442043669]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk989B

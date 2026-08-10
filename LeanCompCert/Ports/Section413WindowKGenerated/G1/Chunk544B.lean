import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk544A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk544B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk544A

def state06 : KState := ⟨⟨362472114093198563, 362472157244840413⟩, ⟨693487806681000713, 695075365950435005⟩, true⟩

def words05 : List Nat := [371284920057782191, 371284920386529653, 371284920646636291, 371284920648469362, 371284920570750249, 371284920585091137, 371284920751312018, 371284920753141524, 371284920520939567, 371284920288651475]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 54450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 54400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482042081124569, 362482085249140724⟩, ⟨152785237311956453, 154373688407796403⟩, true⟩

def words06 : List Nat := [371284920055549354, 371284919995139954, 371284919910489968, 371284920022143281, 371284920078953650, 371284920080783420, 371284919732107869, 371284919494241033, 371284919352036913, 371284919353939840]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 54460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 54400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480321465306141, 362480364650003845⟩, ⟨246530370674386606, 248119730499157032⟩, true⟩

def words07 : List Nat := [371284919303278805, 371284919226734873, 371284919241894183, 371284919243945510, 371284919288077827, 371284919361665891, 371284919433490421, 371284919435320589, 371284919058228331, 371284918976921965]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 54470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 54400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362448998101982674, 362449041303002250⟩, ⟨1953174704678831325, 1954764953803323175⟩, true⟩

def words08 : List Nat := [371284918910510766, 371284918912341040, 371284918480936489, 371284917989490422, 371284917497381950, 371284917034369012, 371284916403877587, 371284915989210783, 371284915573891112, 371284915132215011]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 54480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 54400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488999972532965, 362489043190078513⟩, ⟨(-226739906464415284), (-225148756757121708)⟩, true⟩

def words09 : List Nat := [371284914475114365, 371284914070555512, 371284913665079222, 371284913596582727, 371284913226509266, 371284912773027394, 371284912318782972, 371284912201666295, 371284912018188310, 371284912096029650]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 54490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 54400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 54400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk544B

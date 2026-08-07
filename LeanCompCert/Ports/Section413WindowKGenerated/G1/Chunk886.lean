import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk886

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362460285832849346, 362460404473552948⟩, ⟨2187343827842716687, 2194441166100379939⟩, true⟩

def state01 : KState := ⟨⟨362476212154748190, 362476330823085981⟩, ⟨776205432007339806, 783305218794064640⟩, true⟩

def words00 : List Nat := [371285172155087697, 371285171976179953, 371285171732356491, 371285171605422039, 371285171477586836, 371285171313771613, 371285171042954272, 371285170900995379, 371285170757374230, 371285170742043143]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471782498635368, 362471901195101795⟩, ⟨1168749029448986785, 1175851308854782227⟩, true⟩

def words01 : List Nat := [371285170644589948, 371285170548130090, 371285170450479818, 371285170407099603, 371285170298711511, 371285170214477850, 371285170129144452, 371285170044424575, 371285169805298386, 371285169659431008]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362453837659424980, 362453956383365714⟩, ⟨2759122914692916231, 2766227629016507715⟩, true⟩

def words02 : List Nat := [371285169511819269, 371285169415952343, 371285169168207279, 371285168911021127, 371285168652616249, 371285168433712982, 371285168149980301, 371285167882437935, 371285167613887999, 371285167346121175]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482988604990715, 362483107356898588⟩, ⟨175327767529167187, 182434960718455653⟩, true⟩

def words03 : List Nat := [371285166996070328, 371285166762348873, 371285166526968240, 371285166400378507, 371285166199074542, 371285165985828804, 371285165771358244, 371285165669791187, 371285165532746827, 371285165513043878]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474340952324753, 362474459732151091⟩, ⟨941884431682685405, 948994099705286935⟩, true⟩

def words04 : List Nat := [371285165492199440, 371285165437699147, 371285165277969736, 371285165246900224, 371285165218491213, 371285165221580591, 371285165072100691, 371285164921839920, 371285164770252383, 371285164685334456]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362468746764146954, 362468865571756596⟩, ⟨1437885102850355185, 1444997234003943187⟩, true⟩

def words05 : List Nat := [371285164572989418, 371285164582630004, 371285164584941173, 371285164584654311, 371285164451662129, 371285164299833515, 371285164146363506, 371285164120944659, 371285163938814607, 371285163758469928]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478758899619174, 362478877734881393⟩, ⟨550224797387835799, 557339380362343359⟩, true⟩

def words06 : List Nat := [371285163576739130, 371285163523428224, 371285163446053654, 371285163473221595, 371285163475616160, 371285163471462112, 371285163318273249, 371285163293729060, 371285163277868580, 371285163281067954]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474064077028345, 362474182940472673⟩, ⟨966536488387535850, 973653570412975042⟩, true⟩

def words07 : List Nat := [371285163212507313, 371285163120568360, 371285163027334695, 371285162992565504, 371285162893076041, 371285162832997770, 371285162771868932, 371285162697523711, 371285162464692482, 371285162344739847]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476800513147904, 362476919404177689⟩, ⟨723884807634126020, 731004336079063830⟩, true⟩

def words08 : List Nat := [371285162226227940, 371285162229342615, 371285162147306623, 371285162028712572, 371285161908964624, 371285161829348231, 371285161701174307, 371285161692125652, 371285161681995683, 371285161644972357]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483832504038124, 362483951422936292⟩, ⟨100193646175222396, 107315646412043020⟩, true⟩

def words09 : List Nat := [371285161568995479, 371285161587526853, 371285161668709658, 371285161671801458, 371285161601742645, 371285161517646970, 371285161432303462, 371285161401102015, 371285161305128165, 371285161294936428]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk886

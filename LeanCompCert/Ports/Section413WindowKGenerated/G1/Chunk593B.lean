import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk593A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk593B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk593A

def state06 : KState := ⟨⟨362498794138241701, 362498845757782357⟩, ⟨(-820586364569286627), (-818516576990469051)⟩, true⟩

def words05 : List Nat := [371285056897378405, 371285056965547618, 371285057124301863, 371285057126309424, 371285056945991405, 371285056718776184, 371285056545599244, 371285056547821654, 371285056729566027, 371285056964180658]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473438771560117, 362473490409188531⟩, ⟨684574382746230429, 686645244106562707⟩, true⟩

def words06 : List Nat := [371285057185579702, 371285057187587543, 371285057077072789, 371285057084136821, 371285057161238339, 371285057163246005, 371285056862081869, 371285056458442599, 371285056053981784, 371285055934607204]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476373636897038, 362476425292579408⟩, ⟨510357893607946767, 512429826927123823⟩, true⟩

def words07 : List Nat := [371285055741174882, 371285055735886667, 371285055729954845, 371285055724676586, 371285055483925886, 371285055311271736, 371285055246554774, 371285055248576392, 371285055106051142, 371285054962955413]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477375437074283, 362477427110752284⟩, ⟨450883246434190264, 452956248425872628⟩, true⟩

def words08 : List Nat := [371285054819018077, 371285054728477101, 371285054495405586, 371285054494729183, 371285054493400599, 371285054423140222, 371285054048130540, 371285053958176147, 371285053918715982, 371285053920794815]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488355294067317, 362488406986086715⟩, ⟨(-201254626380319379), (-199180535007794415)⟩, true⟩

def words09 : List Nat := [371285053793893398, 371285053668861886, 371285053699684848, 371285053749045579, 371285053814556785, 371285053880793644, 371285053943499197, 371285053945513476, 371285053775875291, 371285053834877009]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk593B

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk593

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498704066196101, 362498755577255113⟩, ⟨(-814350591532023624), (-812287240176914006)⟩, true⟩

def state01 : KState := ⟨⟨362485829421570406, 362485880950727694⟩, ⟨(-50892035826255587), (-48827611150006613)⟩, true⟩

def words00 : List Nat := [371285058049157643, 371285058051162830, 371285057929067628, 371285057988594881, 371285058099341475, 371285058101356260, 371285057940863994, 371285057771725496, 371285057687398449, 371285057703587198]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474658536269099, 362474710083524340⟩, ⟨611709392024750608, 613774890184106422⟩, true⟩

def words01 : List Nat := [371285057784650150, 371285057866542325, 371285057915408563, 371285057917414704, 371285057641514963, 371285057451664266, 371285057269856417, 371285057271901433, 371285057101435694, 371285056929279298]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483602115138818, 362483653680337038⟩, ⟨81160413500460349, 83226976127399883⟩, true⟩

def words02 : List Nat := [371285056835747695, 371285056837957893, 371285056859702211, 371285056944114452, 371285056971539500, 371285056973545408, 371285056621879088, 371285056484143153, 371285056458907829, 371285056460989784]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484553019236119, 362484604602710602⟩, ⟨24810580237134349, 26878227285631085⟩, true⟩

def words03 : List Nat := [371285056438846218, 371285056416122854, 371285056652058879, 371285056848746713, 371285057129711498, 371285057411452663, 371285057674551246, 371285057676557797, 371285057560814364, 371285057555647671]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472036327115265, 362472087928466143⟩, ⟨767648582706229082, 769717290632923002⟩, true⟩

def words04 : List Nat := [371285057826097983, 371285057828104765, 371285057727661205, 371285057615753464, 371285057503071546, 371285057386649896, 371285057167611123, 371285057126721268, 371285057085172763, 371285057048780093]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk593

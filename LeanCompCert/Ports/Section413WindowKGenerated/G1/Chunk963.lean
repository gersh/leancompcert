import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk963

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362495326268874821, 362495467332895865⟩, ⟨(-990092185327431131), (-980920516136381101)⟩, true⟩

def state01 : KState := ⟨⟨362483982557436097, 362484123651540328⟩, ⟨102368567282446762, 111543133640547830⟩, true⟩

def words00 : List Nat := [371285281515024198, 371285281550594816, 371285281583302641, 371285281617213094, 371285281629812318, 371285281633600029, 371285281679949443, 371285281756723860, 371285281815768554, 371285281819265804]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487270449079965, 362487411573803717⟩, ⟨(-214322606044139475), (-205145090569059791)⟩, true⟩

def words01 : List Nat := [371285281852146571, 371285281898828653, 371285281988409110, 371285281991787339, 371285281937899989, 371285281868780662, 371285281798305322, 371285281786447788, 371285281741291123, 371285281767317395]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481106982343993, 362481248137516167⟩, ⟨379341035848693555, 388521484271421021⟩, true⟩

def words02 : List Nat := [371285281781282825, 371285281784670514, 371285281697271510, 371285281710403565, 371285281755073914, 371285281758452512, 371285281659641862, 371285281528216748, 371285281395388065, 371285281372066893]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488031185917318, 362488172371475445⟩, ⟨(-287666621104327390), (-278483245447997540)⟩, true⟩

def words03 : List Nat := [371285281398532715, 371285281468211269, 371285281535870830, 371285281539309590, 371285281527462577, 371285281540659213, 371285281659914182, 371285281705680329, 371285281738216897, 371285281771985633]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483677987712107, 362483819203538019⟩, ⟨131767069892512510, 140953361699434324⟩, true⟩

def words04 : List Nat := [371285281848952233, 371285281873692733, 371285281967850050, 371285282063400931, 371285282140142161, 371285282143521799, 371285282092173436, 371285282094641538, 371285282130615943, 371285282134121304]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485225862240454, 362485367108880966⟩, ⟨(-17360548146783479), (-8171287201692555)⟩, true⟩

def words05 : List Nat := [371285282121463105, 371285282109568733, 371285282188508638, 371285282235815260, 371285282287871860, 371285282341178644, 371285282392918710, 371285282396298338, 371285282305056415, 371285282310184381]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484170398613910, 362484311675372330⟩, ⟨84380765623718219, 93572928888184335⟩, true⟩

def words06 : List Nat := [371285282410194851, 371285282421838788, 371285282429863812, 371285282438973328, 371285282479140877, 371285282482865689, 371285282532893509, 371285282600155604, 371285282647575025, 371285282651079378]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494312290233787, 362494453597483157⟩, ⟨(-893066415014578643), (-883871313180046467)⟩, true⟩

def words07 : List Nat := [371285282688161583, 371285282737057711, 371285282851878268, 371285282855258456, 371285282826827055, 371285282781956461, 371285282794783531, 371285282804080884, 371285282901526708, 371285283000444529]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487324222579346, 362487465560420484⟩, ⟨(-219548750627614889), (-210350700211406247)⟩, true⟩

def words08 : List Nat := [371285283098498338, 371285283131051898, 371285283206250675, 371285283283212303, 371285283378129733, 371285283381510333, 371285283333048119, 371285283280015379, 371285283268860666, 371285283295476544]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471577446687095, 362471718814959853⟩, ⟨1298402409150333671, 1307603393026875251⟩, true⟩

def words09 : List Nat := [371285283402322189, 371285283510572087, 371285283590655963, 371285283594036753, 371285283530448500, 371285283488786550, 371285283445444935, 371285283440905620, 371285283302371073, 371285283165509925]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk963

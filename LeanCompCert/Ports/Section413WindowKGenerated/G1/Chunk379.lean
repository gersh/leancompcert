import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk379

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486221593003249, 362486241886448150⟩, ⟨(-50454542217629555), (-49934781243973293)⟩, true⟩

def state01 : KState := ⟨⟨362523453070070588, 362523473374597176⟩, ⟨(-1461677842619316720), (-1461157661594323440)⟩, true⟩

def words00 : List Nat := [371284925021953682, 371284925316425024, 371284926126052718, 371284926936158004, 371284927623305279, 371284927691824800, 371284928456102716, 371284929220989288, 371284930570316024, 371284931588266182]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362511837734422001, 362511858050243666⟩, ⟨(-1021178173648429747), (-1020657564370079927)⟩, true⟩

def words01 : List Nat := [371284932604457337, 371284933621046849, 371284935214577533, 371284936497595934, 371284937991166676, 371284939485121224, 371284940837247177, 371284941262997129, 371284941973682880, 371284942685027294]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481057358404127, 362481077685259185⟩, ⟨146226892202251786, 146747919923750904⟩, true⟩

def words02 : List Nat := [371284943859207276, 371284944222875854, 371284944585223623, 371284944947961788, 371284945348005231, 371284945508978318, 371284945882560323, 371284946256642328, 371284946598291087, 371284946599573020]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508166322096707, 362508186660145521⟩, ⟨(-882116867233533923), (-881595414875444357)⟩, true⟩

def words03 : List Nat := [371284947023310426, 371284947549647449, 371284948360724699, 371284948507199838, 371284948554700252, 371284948602590037, 371284949212806973, 371284949476766128, 371284950090084416, 371284950703927303]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485674189992019, 362485694539218137⟩, ⟨(-28744591911556559), (-28222715431623303)⟩, true⟩

def words04 : List Nat := [371284951316248650, 371284951317488085, 371284951402524616, 371284951697836356, 371284952203619114, 371284952204858410, 371284951785631710, 371284951270962504, 371284950856226166, 371284950877247923]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489499801506194, 362489520161888243⟩, ⟨(-173809699961746911), (-173287400056140899)⟩, true⟩

def words05 : List Nat := [371284951591846399, 371284952306928430, 371284953023048349, 371284953164731557, 371284953517304117, 371284953870456371, 371284954916933031, 371284955039288930, 371284955160476881, 371284955282141763]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497418523934099, 362497438895430214⟩, ⟨(-474466630778370622), (-473943908927692738)⟩, true⟩

def words06 : List Nat := [371284955283006394, 371284955270290023, 371284955412876533, 371284955831922951, 371284956139043111, 371284956140283535, 371284955854883726, 371284956060113517, 371284956831757435, 371284957161766953]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491507076356892, 362491527459136533⟩, ⟨(-249983090533776838), (-249459940189978222)⟩, true⟩

def words07 : List Nat := [371284957493075477, 371284957824774137, 371284958414538535, 371284958658639392, 371284958943208484, 371284959228231482, 371284959511759888, 371284959513003473, 371284959265390135, 371284959439858737]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487246293114240, 362487266686955020⟩, ⟨(-88090037742805913), (-87566467239086721)⟩, true⟩

def words08 : List Nat := [371284960116752321, 371284960219992368, 371284960220925800, 371284960196177459, 371284960301945935, 371284960303318735, 371284960747262812, 371284961316607871, 371284961698377360, 371284961760334529]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362533814641582855, 362533835046657502⟩, ⟨(-1857378143572447359), (-1856854146238577661)⟩, true⟩

def words09 : List Nat := [371284962514688002, 371284963269654361, 371284964716734768, 371284965566080668, 371284966208571988, 371284966851427239, 371284968186405975, 371284969175656465, 371284970462447064, 371284971749737985]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk379

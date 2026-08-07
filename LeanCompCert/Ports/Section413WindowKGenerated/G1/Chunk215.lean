import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk215

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504142388175093, 362504148615771482⟩, ⟨(-431258826757931251), (-431168280152256673)⟩, true⟩

def state01 : KState := ⟨⟨362457238707243985, 362457244940900451⟩, ⟨577335424345177737, 577426101272896841⟩, true⟩

def words00 : List Nat := [371284096145968953, 371284096146642776, 371284096050601131, 371284097080881862, 371284097608293495, 371284097608964322, 371284095260932495, 371284092718890945, 371284090176818659, 371284089483033083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362445537855477130, 362445544095186884⟩, ⟨829089651080068783, 829180458245105855⟩, true⟩

def words01 : List Nat := [371284088235551962, 371284087871327819, 371284087506906279, 371284086964855818, 371284084011886327, 371284081404293936, 371284078796600042, 371284078342376206, 371284076575406510, 371284074785625783]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481501951743674, 362481508197462336⟩, ⟨55174448951297732, 55265385458147578⟩, true⟩

def words02 : List Nat := [371284073357784719, 371284073358526014, 371284074511644014, 371284076164564554, 371284077110549996, 371284077111221796, 371284075626231289, 371284074733395865, 371284075098089123, 371284075098784127]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475002758022734, 362475009009858232⟩, ⟨195275144882610097, 195366213116470755⟩, true⟩

def words03 : List Nat := [371284074980067699, 371284074861893577, 371284076395751381, 371284077058829628, 371284078081923938, 371284079105188652, 371284080132382038, 371284080133058567, 371284079356456715, 371284078936186759]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362435810555919691, 362435816813741539⟩, ⟨1039726268725788142, 1039817465936544774⟩, true⟩

def words04 : List Nat := [371284079525801251, 371284079526473441, 371284077670595981, 371284075677089256, 371284073683505831, 371284072195254251, 371284070098995505, 371284069599458340, 371284069099750841, 371284068204272238]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362505692929940129, 362505699193855371⟩, ⟨(-466672536836862675), (-466581208283256719)⟩, true⟩

def words05 : List Nat := [371284065965789854, 371284065232887632, 371284064658468585, 371284064659144208, 371284062767122776, 371284060553666111, 371284058340146595, 371284058272714749, 371284058135178340, 371284059139670350]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474591882123133, 362474598152099034⟩, ⟨203865107755000887, 203956567008054825⟩, true⟩

def words06 : List Nat := [371284060143519177, 371284060144191857, 371284058573405758, 371284058860957901, 371284059523239951, 371284059523913028, 371284057734933933, 371284055681414986, 371284053717721188, 371284053718487910]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362451921017730717, 362451927293759339⟩, ⟨693096118784440626, 693187708625336224⟩, true⟩

def words07 : List Nat := [371284053497759556, 371284053715620408, 371284053716130546, 371284053626561646, 371284052214253823, 371284051440905834, 371284052035645000, 371284052036318308, 371284050547495926, 371284049059682664]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362508964035050104, 362508970317115896⟩, ⟨(-538179270670994473), (-538087550517810075)⟩, true⟩

def words08 : List Nat := [371284047571719921, 371284046976535525, 371284046366384890, 371284047040832343, 371284047349470932, 371284047350144747, 371284045201662620, 371284045193934482, 371284047317319238, 371284048472341786]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483204340077958, 362483210628290575⟩, ⟨18111359891489396, 18203212784814802⟩, true⟩

def words09 : List Nat := [371284049633937553, 371284050795653614, 371284052499480335, 371284053244461146, 371284054076463072, 371284054908630867, 371284055584219149, 371284055584893314, 371284053407788147, 371284053369623206]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk215

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk795

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479074039350292, 362479168767068144⟩, ⟨474810591107119546, 479895921054845388⟩, true⟩

def state01 : KState := ⟨⟨362475356611822896, 362475451364015527⟩, ⟨770392161452540494, 775479437273070368⟩, true⟩

def words00 : List Nat := [371285205187106662, 371285205189853504, 371285205066073591, 371285204943240517, 371285204819322020, 371285204745185761, 371285204612885747, 371285204614006634, 371285204614195887, 371285204595524433]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484857407824081, 362484952184901365⟩, ⟨14927602353020135, 20016856875166367⟩, true⟩

def words01 : List Nat := [371285204474725023, 371285204467423926, 371285204488409933, 371285204491157313, 371285204332625005, 371285204170811055, 371285204007907631, 371285203988615245, 371285203905922301, 371285203905938528]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476931872635836, 362477026674480355⟩, ⟨645161215991009792, 650252440131083588⟩, true⟩

def words02 : List Nat := [371285203904836621, 371285203902447261, 371285203688513919, 371285203625717193, 371285203561563561, 371285203545225244, 371285203366313702, 371285203154466984, 371285202941482900, 371285202865101896]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484441075675126, 362484535902220144⟩, ⟨47985427708335594, 53078616405838022⟩, true⟩

def words03 : List Nat := [371285202819299738, 371285202877395556, 371285202934361730, 371285202937181188, 371285202979174568, 371285203026805152, 371285203230892590, 371285203233640795, 371285203227340429, 371285203222014032]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483261964386445, 362483356815562667⟩, ⟨141763900256798495, 146859048245612357⟩, true⟩

def words04 : List Nat := [371285203225647680, 371285203228707987, 371285203196563241, 371285203232683134, 371285203242491229, 371285203245241842, 371285203076582240, 371285202978433227, 371285202935253507, 371285202938105038]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479676841648548, 362479771717922653⟩, ⟨426986131250523918, 432083275894136724⟩, true⟩

def words05 : List Nat := [371285202916972206, 371285202896600001, 371285202942345440, 371285202945374573, 371285202935650988, 371285202933678592, 371285202930805665, 371285202917911437, 371285202693655106, 371285202628881604]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479850879606951, 362479945780374103⟩, ⟨413177081544604256, 418276174984876306⟩, true⟩

def words06 : List Nat := [371285202652074093, 371285202654871009, 371285202615349978, 371285202547330008, 371285202478283453, 371285202458803277, 371285202413653485, 371285202465954333, 371285202484514704, 371285202487361472]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497753727019537, 362497848652619603⟩, ⟨(-1011439065453304771), (-1006337995933625835)⟩, true⟩

def words07 : List Nat := [371285202491162882, 371285202562428103, 371285202736766629, 371285202770346565, 371285202778941154, 371285202788470055, 371285202870163449, 371285202874355415, 371285203035126678, 371285203197097134]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482101444553053, 362482196394988188⟩, ⟨234179929083664896, 239282975106058220⟩, true⟩

def words08 : List Nat := [371285203345330920, 371285203348080762, 371285203287060998, 371285203291656488, 371285203300124651, 371285203302887776, 371285203160466623, 371285203001417633, 371285202841277841, 371285202840208770]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466217630690752, 362466312605915806⟩, ⟨1498504450614435598, 1503609469790428932⟩, true⟩

def words09 : List Nat := [371285202845358139, 371285202889419737, 371285202926818550, 371285202929576516, 371285202805235594, 371285202730724391, 371285202654795025, 371285202636026685, 371285202406296832, 371285202172119204]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk795

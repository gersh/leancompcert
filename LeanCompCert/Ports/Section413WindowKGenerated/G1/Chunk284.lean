import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk284

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482728583917268, 362482739708595539⟩, ⟨65458147950997440, 65671718886552118⟩, true⟩

def state01 : KState := ⟨⟨362478489570522311, 362478500703375284⟩, ⟨185787604618887386, 186001407758304024⟩, true⟩

def words00 : List Nat := [371285052012322227, 371285051934640831, 371285050809403845, 371285050866173017, 371285050929786866, 371285050930708832, 371285049964724007, 371285048812066372, 371285047742389984, 371285047743423095]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362460151761964001, 362460162902984104⟩, ⟨706957358687663196, 707171393896137302⟩, true⟩

def words01 : List Nat := [371285048519813764, 371285049526933266, 371285050002942852, 371285050003849514, 371285048831349072, 371285048033038532, 371285047532329195, 371285047533240182, 371285046655568248, 371285045781024081]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478329624048888, 362478340773180168⟩, ⟨190366886677981114, 190581152447013950⟩, true⟩

def words02 : List Nat := [371285045073553682, 371285045074561724, 371285045223891115, 371285045816056168, 371285046193931297, 371285046194838359, 371285045110091424, 371285044427232432, 371285044295014886, 371285044295953542]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494353708348159, 362494364865758528⟩, ⟨(-265237164002421619), (-265022662817124777)⟩, true⟩

def words03 : List Nat := [371285044060860322, 371285043815446995, 371285044557977238, 371285045105392823, 371285045663465152, 371285046221831985, 371285046782983076, 371285046783890648, 371285046205587280, 371285046534377173]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460659996174236, 362460671161683642⟩, ⟨693118454307086296, 693333185870928166⟩, true⟩

def words04 : List Nat := [371285047033486587, 371285047034394091, 371285045888387686, 371285044706937571, 371285043525227732, 371285042717118337, 371285041478966408, 371285041474854998, 371285041470415804, 371285041396687893]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492824921435448, 362492836095135781⟩, ⟨(-222127118359033692), (-221912153721102640)⟩, true⟩

def words05 : List Nat := [371285040562754454, 371285040585846041, 371285041560064285, 371285041560972550, 371285041113104909, 371285040370888264, 371285039628354867, 371285039278502270, 371285038759138413, 371285039034114696]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482974693001268, 362482985874907001⟩, ⟨58277355775630907, 58492553980943845⟩, true⟩

def words06 : List Nat := [371285039275908856, 371285039276834724, 371285039484179229, 371285040204658871, 371285041298189030, 371285041299097749, 371285040963073420, 371285040615679932, 371285040406848013, 371285040407888419]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467178000741633, 362467189190839918⟩, ⟨508239583368755742, 508455014857474788⟩, true⟩

def words07 : List Nat := [371285041312034744, 371285042288651096, 371285043267975231, 371285043268885335, 371285042926733660, 371285042627823304, 371285043259371613, 371285043260281295, 371285042871988382, 371285042246136880]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484270757721563, 362484281955964333⟩, ⟨21339899295738153, 21555562781394761⟩, true⟩

def words08 : List Nat := [371285041895293230, 371285041896294863, 371285041703177985, 371285041754871034, 371285041755582178, 371285041594707292, 371285039793556926, 371285039042782407, 371285038556010454, 371285038556974561]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486512050330748, 362486523256846991⟩, ⟨(-42455437039158511), (-42239537800751183)⟩, true⟩

def words09 : List Nat := [371285038531099352, 371285038508804536, 371285039692286735, 371285040292297393, 371285041059958314, 371285041827928705, 371285042290165997, 371285042291075809, 371285041166682594, 371285041219802651]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk284

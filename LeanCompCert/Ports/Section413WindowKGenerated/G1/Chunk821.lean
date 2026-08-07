import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk821

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500755160228887, 362500856434879085⟩, ⟨(-1287738912959932357), (-1282124540831428741)⟩, true⟩

def state01 : KState := ⟨⟨362485349987220156, 362485451287566147⟩, ⟨(-22957640265271525), (-17341158383324939)⟩, true⟩

def words00 : List Nat := [371285240196887227, 371285240199731132, 371285240227626430, 371285240264613800, 371285240345635322, 371285240348479888, 371285240252492092, 371285240157710822, 371285240090019005, 371285240095906281]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472532905662504, 362472634231619458⟩, ⟨1029568465937242876, 1035187050869320636⟩, true⟩

def words01 : List Nat := [371285240234720031, 371285240374729181, 371285240505053311, 371285240507898096, 371285240440421797, 371285240380711361, 371285240319560235, 371285240320324895, 371285240166740914, 371285240016457127]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484689418867917, 362484790770294889⟩, ⟨31225072852699867, 36845749510932121⟩, true⟩

def words02 : List Nat := [371285239864893432, 371285239813118763, 371285239686101334, 371285239672363121, 371285239657734718, 371285239626245322, 371285239461326789, 371285239391285095, 371285239394518639, 371285239397465362]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489806803358821, 362489908180707189⟩, ⟨(-389103678979031421), (-383480873264818429)⟩, true⟩

def words03 : List Nat := [371285239394167278, 371285239363176393, 371285239402703231, 371285239421267201, 371285239484128100, 371285239548102919, 371285239581758916, 371285239584654133, 371285239552020022, 371285239612351985]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482462133604386, 362482563536286884⟩, ⟨214249831647004638, 219874718436923392⟩, true⟩

def words04 : List Nat := [371285239819352037, 371285239850937318, 371285239881468023, 371285239912987801, 371285239950526232, 371285239953662369, 371285239953341248, 371285239992648855, 371285240036297441, 371285240039250207]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491021247571432, 362491122676061384⟩, ⟨(-488873550174572633), (-483246543178353399)⟩, true⟩

def words05 : List Nat := [371285240113992970, 371285240222906953, 371285240478428853, 371285240537367654, 371285240571532275, 371285240606568423, 371285240752334943, 371285240825346552, 371285240898914604, 371285240973755201]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487885842795160, 362487987296963685⟩, ⟨(-231310691507554121), (-225681574628278279)⟩, true⟩

def words06 : List Nat := [371285241028298260, 371285241031144528, 371285240891111441, 371285240897592053, 371285240948111335, 371285240951007431, 371285240878849106, 371285240800474161, 371285240773344071, 371285240810068938]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481742115346920, 362481843595153314⟩, ⟨273601018622065708, 279232242295194314⟩, true⟩

def words07 : List Nat := [371285240993563571, 371285241178186527, 371285241339238230, 371285241342084934, 371285241330013654, 371285241343086072, 371285241468710215, 371285241471564716, 371285241445907398, 371285241407787717]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490804563755398, 362490906069012893⟩, ⟨(-471181148152776545), (-465547832775261885)⟩, true⟩

def words08 : List Nat := [371285241389290012, 371285241392427442, 371285241436448767, 371285241534660791, 371285241607871519, 371285241610734962, 371285241593976368, 371285241612702711, 371285241778040317, 371285241849904046]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494093054999594, 362494194586231169⟩, ⟨(-741448620938037987), (-735813170621042191)⟩, true⟩

def words09 : List Nat := [371285241920807798, 371285241992730010, 371285242211513505, 371285242390744316, 371285242580218570, 371285242770747749, 371285242960051959, 371285242973405371, 371285243084246473, 371285243196702806]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk821

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk374

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362526346826437597, 362526366566500646⟩, ⟨(-1553805240508006131), (-1553306314735206469)⟩, true⟩

def state01 : KState := ⟨⟨362506313290897358, 362506333041976408⟩, ⟨(-804574261558238902), (-804074923730964498)⟩, true⟩

def words00 : List Nat := [371284836419412784, 371284836463852596, 371284837153960054, 371284837844661688, 371284838748795878, 371284838804168575, 371284838805081472, 371284838785122242, 371284839458019132, 371284840033937838]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471957320525944, 362471977082570690⟩, ⟨480933761311826168, 481433509423244748⟩, true⟩

def words01 : List Nat := [371284840843751763, 371284841654000300, 371284842467293057, 371284842598252179, 371284842769554533, 371284842941445831, 371284843437908438, 371284843439129719, 371284843098726993, 371284842756259179]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486913584156539, 362486933357148649⟩, ⟨(-78675609160842243), (-78175451343678815)⟩, true⟩

def words02 : List Nat := [371284842584337668, 371284842585729067, 371284843258438292, 371284843952837056, 371284844534707161, 371284844535928295, 371284844271643865, 371284844378549908, 371284844778501705, 371284844835566440]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476108733003732, 362476128517148942⟩, ⟨325837250474063644, 326337825805443354⟩, true⟩

def words03 : List Nat := [371284844896017143, 371284844956878733, 371284845230271465, 371284845231620410, 371284845406293299, 371284845601436600, 371284845793801549, 371284845795023178, 371284845036492917, 371284844805231353]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477271512250684, 362477291307285873⟩, ⟨282308788466290868, 282809771574445428⟩, true⟩

def words04 : List Nat := [371284845053911245, 371284845055133061, 371284844676916932, 371284844163547001, 371284843649736987, 371284843350337520, 371284842800917829, 371284842883776829, 371284842968790279, 371284842970078249]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484975182867430, 362484994988924876⟩, ⟨(-6243684048341303), (-5742288099003855)⟩, true⟩

def words05 : List Nat := [371284843010954858, 371284843254075994, 371284843822946068, 371284843824168367, 371284843555016527, 371284843032216696, 371284842508947010, 371284842279552048, 371284841696370807, 371284841701823651]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478745301453976, 362478765118540308⟩, ⟨227066835699344547, 227568644846421193⟩, true⟩

def words06 : List Nat := [371284841704676564, 371284841705898877, 371284840759143754, 371284840525680313, 371284840291590723, 371284840169842281, 371284839632839131, 371284839042865397, 371284838473027255, 371284838474420918]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362455096220797059, 362455116048916138⟩, ⟨1113350834011094527, 1113853056612168619⟩, true⟩

def words07 : List Nat := [371284838340637198, 371284838369432608, 371284838395891907, 371284838397115312, 371284837605908602, 371284837031834467, 371284836457162903, 371284836242300250, 371284835438567250, 371284834647011447]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476882550759857, 362476902389819187⟩, ⟨296740888432424736, 297243521129496100⟩, true⟩

def words08 : List Nat := [371284833854944251, 371284833609064841, 371284833118832757, 371284833230530200, 371284833231504807, 371284833091460275, 371284832002722783, 371284831430897120, 371284830996743627, 371284830998011492]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463881091781623, 362463900941980889⟩, ⟨784367387585339860, 784870437975339938⟩, true⟩

def words09 : List Nat := [371284830787445780, 371284830575479426, 371284830861111849, 371284831004259048, 371284831360375716, 371284831716952689, 371284832020243615, 371284832021467181, 371284831376969727, 371284830820326899]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk374

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk647

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494439056761756, 362494500799772260⟩, ⟨(-582293259864806019), (-579595096859811967)⟩, true⟩

def state01 : KState := ⟨⟨362491926071016621, 362491987833943968⟩, ⟨(-419724185651078088), (-417024733924464434)⟩, true⟩

def words00 : List Nat := [371285542855788784, 371285542858011557, 371285542981101702, 371285543149067516, 371285543388725229, 371285543390927202, 371285543312488766, 371285543234460404, 371285543313808631, 371285543415932742]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483735126102958, 362483796908863844⟩, ⟨110426954368867669, 113127689625956673⟩, true⟩

def words01 : List Nat := [371285543725099499, 371285544035171756, 371285544287327426, 371285544373955560, 371285544462102503, 371285544551283431, 371285544878001667, 371285544887349396, 371285544889018182, 371285544864513195]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488597052264819, 362488658854770781⟩, ⟨(-204172917014370332), (-201470903758103554)⟩, true⟩

def words02 : List Nat := [371285545015015297, 371285545125459345, 371285545432249099, 371285545739920887, 371285546009159442, 371285546011362240, 371285546064584559, 371285546169443162, 371285546371357378, 371285546421720804]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483660892452826, 362483722715006619⟩, ⟨115397534029010804, 118100845082160784⟩, true⟩

def words03 : List Nat := [371285546471125972, 371285546521253046, 371285546744301743, 371285546849153862, 371285546958879626, 371285547069514529, 371285547179407389, 371285547181610424, 371285546973478520, 371285546948016848]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479743990479317, 362479805832674040⟩, ⟨368982801289339789, 371687383997695021⟩, true⟩

def words04 : List Nat := [371285547096194149, 371285547098397446, 371285546957122668, 371285546770331172, 371285546582684658, 371285546418924767, 371285546177693398, 371285546175749201, 371285546176048315, 371285546178372847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482461255504028, 362482523117621256⟩, ⟨193043082951949891, 195748955742254661⟩, true⟩

def words05 : List Nat := [371285546216259176, 371285546343971451, 371285546571964146, 371285546574167701, 371285546484665864, 371285546355201297, 371285546224902395, 371285546088853399, 371285545844873799, 371285545800693249]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481335312990729, 362481397195007596⟩, ⟨265903824598864594, 268610986187978134⟩, true⟩

def words06 : List Nat := [371285545755666338, 371285545710874839, 371285545347760304, 371285545224116713, 371285545099341563, 371285545047978351, 371285544818612027, 371285544589754083, 371285544359955421, 371285544346253358]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469284076780565, 362469345978633615⟩, ⟨1046541858538753340, 1049250305020393452⟩, true⟩

def words07 : List Nat := [371285544285769300, 371285544290160078, 371285544294607289, 371285544296811800, 371285544005314997, 371285543785828251, 371285543565186824, 371285543561110003, 371285543359665757, 371285543112085613]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487849853919963, 362487911775496589⟩, ⟨(-156199717345109853), (-153489993069681105)⟩, true⟩

def words08 : List Nat := [371285542863552137, 371285542854108919, 371285542856823816, 371285542978911583, 371285543040438367, 371285543042645131, 371285542846828130, 371285542744175136, 371285542734867111, 371285542773736010]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486660972392313, 362486722914122806⟩, ⟨(-79117748487228664), (-76406718348062456)⟩, true⟩

def words09 : List Nat := [371285542794600415, 371285542816264035, 371285543075012052, 371285543215755877, 371285543428269255, 371285543641600619, 371285543853927921, 371285543856133448, 371285543795302596, 371285543816294871]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk647

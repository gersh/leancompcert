import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk486

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486260045725503, 362486294096925620⟩, ⟨(-61099799714571134), (-59981732337903758)⟩, true⟩

def state01 : KState := ⟨⟨362461314576284706, 362461348641923455⟩, ⟨1151393253742922140, 1152512022910988296⟩, true⟩

def words00 : List Nat := [371285060087363815, 371285060088985945, 371285059808568291, 371285059468544239, 371285059127928479, 371285058919179440, 371285058497492846, 371285058358090040, 371285058218111545, 371285058002608726]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500262182356943, 362500296262605866⟩, ⟨(-742040398482548840), (-740920919040822040)⟩, true⟩

def words01 : List Nat := [371285057515970962, 371285057452028720, 371285057707983256, 371285057709602457, 371285057523019888, 371285057243185332, 371285057037507467, 371285057039309074, 371285057245576773, 371285057560830074]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492478979585253, 362492513074446107⟩, ⟨(-363570755907234860), (-362450565957598348)⟩, true⟩

def words02 : List Nat := [371285057857282942, 371285057879933957, 371285058323685648, 371285058768278630, 371285059337681933, 371285059418537343, 371285059500756255, 371285059583490901, 371285059842782996, 371285059997890873]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467810218393322, 362467844327862753⟩, ⟨836252813832859405, 837373714270225005⟩, true⟩

def words03 : List Nat := [371285060370358919, 371285060743476489, 371285061094934967, 371285061096554985, 371285060885167541, 371285060759371751, 371285060776721225, 371285060778341528, 371285060422445970, 371285060070343638]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362495340134527136, 362495374258510926⟩, ⟨(-502930187622241090), (-501808581131700104)⟩, true⟩

def words04 : List Nat := [371285059737673591, 371285059739470896, 371285059685150188, 371285059747793944, 371285059749061872, 371285059704100688, 371285059254211243, 371285059226396679, 371285059589153474, 371285059802875242]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479588825817775, 362479622964539219⟩, ⟨263514892647268229, 264637216200972391⟩, true⟩

def words05 : List Nat := [371285060017808209, 371285060233264000, 371285060666090291, 371285060941266536, 371285061281764823, 371285061622889047, 371285061876967762, 371285061878588257, 371285061570336134, 371285061460556502]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478714426786511, 362478748579930580⟩, ⟨306113937033396234, 307236962467029842⟩, true⟩

def words06 : List Nat := [371285061659120209, 371285061660742350, 371285061512629512, 371285061362343812, 371285061211387496, 371285061191881036, 371285061049794504, 371285061141392819, 371285061234147612, 371285061235826759]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502464012790128, 362502498180634458⟩, ⟨(-849978078331984260), (-848854337366008826)⟩, true⟩

def words07 : List Nat := [371285061107248499, 371285061042209981, 371285061330037256, 371285061331658347, 371285061124822811, 371285060758800616, 371285060445124310, 371285060446945580, 371285060743766921, 371285061103800252]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489872969499220, 362489907151974565⟩, ⟨(-237056189396505031), (-235931736117090045)⟩, true⟩

def words08 : List Nat := [371285061454060085, 371285061455681686, 371285061479349727, 371285061673948252, 371285061875774790, 371285061877407411, 371285061701326263, 371285061527512863, 371285061560949812, 371285061662333418]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362462802562062093, 362462836759140098⟩, ⟨1081208982128709976, 1082334146487302962⟩, true⟩

def words09 : List Nat := [371285061942840045, 371285062224008382, 371285062506320141, 371285062507942251, 371285062277069473, 371285062177794882, 371285062106230678, 371285062107860482, 371285061734158455, 371285061279601850]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk486

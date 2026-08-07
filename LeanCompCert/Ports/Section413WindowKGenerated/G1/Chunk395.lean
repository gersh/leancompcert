import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk395

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362515905968800873, 362515928086302317⟩, ⟨(-1214266371620818420), (-1213676008797197418)⟩, true⟩

def state01 : KState := ⟨⟨362491500142716579, 362491522271919343⟩, ⟨(-250233562235768311), (-249642737150697183)⟩, true⟩

def words00 : List Nat := [371285203454635275, 371285203455929051, 371285203519044341, 371285203872077517, 371285204418665441, 371285204419959290, 371285204113148130, 371285203796141907, 371285203800748122, 371285203962153691]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478059395213297, 362478081536073955⟩, ⟨281011011190565318, 281602296937056168⟩, true⟩

def words01 : List Nat := [371285204763440669, 371285205565233897, 371285206366328359, 371285206479102857, 371285206630689074, 371285206782877538, 371285207456782540, 371285207458076847, 371285207279092792, 371285207100267707]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481214724729481, 362481236877187379⟩, ⟨156422905839804766, 157014649967575364⟩, true⟩

def words02 : List Nat := [371285207380734083, 371285207609094566, 371285208163450627, 371285208718287741, 371285209142958517, 371285209144253085, 371285208716165994, 371285208695338215, 371285208913538996, 371285208914879451]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483853122700213, 362483875286936851⟩, ⟨52156907056345814, 52749116858803692⟩, true⟩

def words03 : List Nat := [371285208815368322, 371285208716222927, 371285208939097416, 371285209040563293, 371285209335565090, 371285209631088785, 371285209884764557, 371285209886059888, 371285209388812349, 371285209356660139]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481256447338892, 362481278623124523⟩, ⟨154871357348422816, 155464023858311578⟩, true⟩

def words04 : List Nat := [371285209929406309, 371285209930705010, 371285209886617242, 371285209711966589, 371285209536823994, 371285209389191924, 371285209146063824, 371285209295213353, 371285209444106893, 371285209445472395]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499756346370334, 362499778533876198⟩, ⟨(-576817180795088507), (-576224050692987169)⟩, true⟩

def words05 : List Nat := [371285209886625510, 371285210427826901, 371285211466478346, 371285211654182551, 371285211755319609, 371285211856844430, 371285212220074418, 371285212337969711, 371285212707060597, 371285213076716547]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483681356425576, 362483703555613832⟩, ⟨59118304130133199, 59711896447851809⟩, true⟩

def words06 : List Nat := [371285213446203424, 371285213447499299, 371285213289885814, 371285213531521397, 371285213878821456, 371285213880117548, 371285213482337115, 371285212967189188, 371285212573505771, 371285212574983250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476681742793258, 362476703953651476⟩, ⟨336148404399825699, 336742458558096055⟩, true⟩

def words07 : List Nat := [371285212761778103, 371285212987202582, 371285213211641393, 371285213212938005, 371285212711681582, 371285212405438514, 371285212255054013, 371285212256381589, 371285212061522210, 371285211848006153]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484057422221898, 362484079644678291⟩, ⟨44312284777183193, 44906798050592223⟩, true⟩

def words08 : List Nat := [371285212057100003, 371285212168097905, 371285212735368624, 371285213303154611, 371285213759342286, 371285213760639007, 371285213499100341, 371285213633040054, 371285213939825465, 371285213941168582]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478502256843324, 362478524491163516⟩, ⟨264316546371886142, 264911529388622034⟩, true⟩

def words09 : List Nat := [371285213913497160, 371285213876973039, 371285214170157297, 371285214182849721, 371285214388241443, 371285214594110319, 371285214772318623, 371285214773621992, 371285214343533345, 371285214176249088]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk395

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk226

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360547705599574737, 360547708596464783⟩, ⟨737297412271779889, 737343237257150467⟩, true⟩

def state01 : KState := ⟨⟨360577999491598719, 360578002491255084⟩, ⟨52444540207653182, 52490427725434482⟩, true⟩

def words00 : List Nat := [360580332960103905, 360580333676940363, 360580334460404898, 360580335243851902, 360580335244123415, 360580334056579382, 360580331610509863, 360580328797229978, 360580325984111042, 360580324049314591]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594830158409970, 360594833160852228⟩, ⟨(-328190833375678015), (-328144882854832637)⟩, true⟩

def words01 : List Nat := [360580323946901620, 360580322860582173, 360580322637387765, 360580324477658177, 360580325821577141, 360580327165426856, 360580327165694622, 360580326979017441, 360580326313352677, 360580326954987995]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564321058277694, 360564324063476759⟩, ⟨362083582077264124, 362129594971087754⟩, true⟩

def words02 : List Nat := [360580329544796092, 360580330193735801, 360580330193996753, 360580329860556752, 360580329527093880, 360580328761806292, 360580328762045489, 360580328327833934, 360580327893629420, 360580326255035358]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611319630285518, 360611322638253513⟩, ⟨(-702189662380596378), (-702143586812279794)⟩, true⟩

def words03 : List Nat := [360580325548184894, 360580324238178133, 360580322928202238, 360580322186381855, 360580319505348697, 360580315166008505, 360580310826995822, 360580308434185740, 360580309228638849, 360580310598731749]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557035221385304, 360557038232143695⟩, ⟨526858509474894877, 526904648231533227⟩, true⟩

def words04 : List Nat := [360580310987997131, 360580310988290197, 360580309835049532, 360580310231125908, 360580310231375482, 360580309291958252, 360580308131966937, 360580305992258974, 360580303852685266, 360580301130520364]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360479679647430991, 360479682660954030⟩, ⟨2279663556902196574, 2279709758291995450⟩, true⟩

def words05 : List Nat := [360580301020675610, 360580301937824975, 360580301938088876, 360580301859975751, 360580300584884053, 360580298258848790, 360580295932933343, 360580294994606633, 360580292120831760, 360580287681178743]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564346680310380, 360564349696600146⟩, ⟨360514682215718748, 360560946313752728⟩, true⟩

def words06 : List Nat := [360580283241850430, 360580278469214077, 360580274689664063, 360580272323990112, 360580269958502075, 360580265933664962, 360580261960359510, 360580258812498111, 360580255664828921, 360580254458237277]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561311188193385, 360561314207286338⟩, ⟨429014986895983561, 429061314555661885⟩, true⟩

def words07 : List Nat := [360580253756956456, 360580251521743255, 360580249286674124, 360580246335545017, 360580244356411799, 360580241850263586, 360580239344304504, 360580235861870734, 360580233088487689, 360580232254665336]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360545240945977730, 360545243967834353⟩, ⟨793611930076528399, 793658320430326427⟩, true⟩

def words08 : List Nat := [360580231652432541, 360580231652728116, 360580231612342098, 360580230596289658, 360580229580280134, 360580227444359490, 360580226463631708, 360580225402981912, 360580224342396054, 360580222298395408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360672584952362144, 360672587976992092⟩, ⟨(-2096627971640900892), (-2096581518346623522)⟩, true⟩

def words09 : List Nat := [360580221152923701, 360580221549009845, 360580222218054132, 360580222935292085, 360580222935563735, 360580221763260100, 360580221354671586, 360580223488219183, 360580227557377257, 360580231626243376]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk226

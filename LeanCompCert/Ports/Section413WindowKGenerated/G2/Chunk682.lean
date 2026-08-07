import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk682

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567252019854034, 360567281935520903⟩, ⟨1058273026739180355, 1059651174665455345⟩, true⟩

def state01 : KState := ⟨⟨360600664167033170, 360600694091807385⟩, ⟨(-1220670713981827735), (-1219291944890224515)⟩, true⟩

def words00 : List Nat := [360582819115749211, 360582818884411168, 360582818823601282, 360582818883552230, 360582818884441329, 360582818761472125, 360582818489296216, 360582818432063989, 360582818530846946, 360582818793909829]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600886030953637, 360600915964910991⟩, ⟨(-1235842273698927784), (-1234462878179078998)⟩, true⟩

def words01 : List Nat := [360582818876541342, 360582818959257408, 360582819256394407, 360582819661937620, 360582819918388544, 360582820174975214, 360582820323957581, 360582820375601739, 360582820641634769, 360582820907990409]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360617383023887607, 360617412966941641⟩, ⟨(-2361331481232693616), (-2359951465092082942)⟩, true⟩

def words02 : List Nat := [360582821246900727, 360582821697704246, 360582822040911910, 360582822384219741, 360582822672878126, 360582823083562264, 360582823708473044, 360582824333550770, 360582824786768639, 360582825294694539]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360626178006151119, 360626207958306396⟩, ⟨(-2961529935175172315), (-2960149298011144761)⟩, true⟩

def words03 : List Nat := [360582825889714660, 360582826484999623, 360582827112844295, 360582827573870865, 360582827852179256, 360582828130571402, 360582828391814869, 360582828814131427, 360582829450596208, 360582830087260967]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604663408526227, 360604693369882485⟩, ⟨(-1493425334832256706), (-1492044069750207158)⟩, true⟩

def words04 : List Nat := [360582830574752736, 360582830906364725, 360582831233187892, 360582831560278433, 360582831832823245, 360582831891136402, 360582831892003796, 360582831842680443, 360582831917185225, 360582832238620669]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360556495680544113, 360556525650975353⟩, ⟨1794359932859524343, 1795741817355400737⟩, true⟩

def words05 : List Nat := [360582832728156272, 360582833217862373, 360582833600086253, 360582833768060836, 360582833768875966, 360582833739913218, 360582833710671164, 360582833670672837, 360582833416239793, 360582833031833182]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589842354423538, 360589872333961453⟩, ⟨(-482053212192306787), (-480670706030819225)⟩, true⟩

def words06 : List Nat := [360582832647219220, 360582832477197082, 360582832429613798, 360582832369326456, 360582832308956558, 360582832034473721, 360582831811161615, 360582831682385986, 360582831601952936, 360582831706080936]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596413877187679, 360596443865928304⟩, ⟨(-930779571326375509), (-929396436849361541)⟩, true⟩

def words07 : List Nat := [360582831706955625, 360582831644352692, 360582831670195264, 360582831867174928, 360582832009613997, 360582832152210053, 360582832153075660, 360582832132417092, 360582832317714997, 360582832518161732]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587194314977170, 360587224312804003⟩, ⟨(-301218380638248790), (-299834625709739284)⟩, true⟩

def words08 : List Nat := [360582832932461655, 360582833132742871, 360582833224103339, 360582833315557868, 360582833316379662, 360582833335831487, 360582833514317806, 360582833692989253, 360582833703725883, 360582833769017710]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589104476115736, 360589134483063198⟩, ⟨(-431645342089573277), (-430260964267621339)⟩, true⟩

def words09 : List Nat := [360582833978603054, 360582834188493793, 360582834526469567, 360582834650492554, 360582834651383682, 360582834582414303, 360582834609203307, 360582834814148311, 360582834907183151, 360582835000416274]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk682

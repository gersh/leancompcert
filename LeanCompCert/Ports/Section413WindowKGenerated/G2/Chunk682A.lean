import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk682A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk682A

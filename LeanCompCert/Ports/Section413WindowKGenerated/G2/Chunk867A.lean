import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk867A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360560418732811747, 360560468000009507⟩, ⟨1879944456216955749, 1882829023144130403⟩, true⟩

def state01 : KState := ⟨⟨360581611522063140, 360581660801024363⟩, ⟨42433860903315531, 45319447780935859⟩, true⟩

def words00 : List Nat := [360582184348270256, 360582184210727881, 360582184144417997, 360582184011697011, 360582183878775607, 360582183712692263, 360582183612891663, 360582183594743229, 360582183576478230, 360582183456401839]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598377786761333, 360598427077488342⟩, ⟨(-1411489010777894892), (-1408602403630695452)⟩, true⟩

def words01 : List Nat := [360582183578202883, 360582183706394979, 360582183854898900, 360582183903220251, 360582183904382391, 360582183829424773, 360582183754208003, 360582183778983154, 360582183967298896, 360582184155893450]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584046730000955, 360584096032626809⟩, ⟨(-168773711095047219), (-165886072024391711)⟩, true⟩

def words02 : List Nat := [360582184268911443, 360582184282263517, 360582184283294476, 360582184241725963, 360582184199804994, 360582184123602061, 360582183949367014, 360582183708749425, 360582183467897553, 360582183382340010]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556614002287133, 360556663316659069⟩, ⟨2210662970331974372, 2213551628199470196⟩, true⟩

def words03 : List Nat := [360582183490278149, 360582183598452624, 360582183619527652, 360582183620778733, 360582183597665428, 360582183468708946, 360582183339399969, 360582183206858934, 360582182996574060, 360582182703656988]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589229155712306, 360589278481858477⟩, ⟨(-618505756226704897), (-615616077003375187)⟩, true⟩

def words04 : List Nat := [360582182410463564, 360582182224699525, 360582182149904101, 360582182179645745, 360582182180796678, 360582182097451269, 360582181995697237, 360582181999102763, 360582182041636935, 360582182124732872]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk867A

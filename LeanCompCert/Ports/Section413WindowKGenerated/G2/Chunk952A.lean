import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk952A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579764338916875, 360579824172797439⟩, ⟨219045915218144208, 222892277482533526⟩, true⟩

def state01 : KState := ⟨⟨360582645027839158, 360582704874732917⟩, ⟨(-55176956211798137), (-51329355027686049)⟩, true⟩

def words00 : List Nat := [360582165454756542, 360582165512395289, 360582165690422185, 360582165868710069, 360582165935849785, 360582165937229745, 360582165915876784, 360582165847067368, 360582165777856364, 360582165763127875]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583298193471059, 360583358053518323⟩, ⟨(-117362473000981868), (-113513619407754008)⟩, true⟩

def words01 : List Nat := [360582165764368722, 360582165702357903, 360582165686984238, 360582165821079363, 360582165911314931, 360582166001783343, 360582166015181267, 360582166016561356, 360582165932420368, 360582165946531338]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569497733903496, 360569557606960403⟩, ⟨1196733161577137858, 1200583254013118866⟩, true⟩

def words02 : List Nat := [360582165947666435, 360582165933878532, 360582165845974633, 360582165702820904, 360582165559451697, 360582165355673395, 360582165220231583, 360582165099747215, 360582164979100051, 360582164802739182]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360605430491712569, 360605490377797272⟩, ⟨(-2225352700210696874), (-2221501367074486572)⟩, true⟩

def words03 : List Nat := [360582164671469178, 360582164650877335, 360582164718032319, 360582164769774700, 360582164771069596, 360582164717365276, 360582164696271986, 360582164832491035, 360582165078519894, 360582165324857105]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581731712209858, 360581791611448394⟩, ⟨31812294320228718, 35664880291800156⟩, true⟩

def words04 : List Nat := [360582165506589197, 360582165691054997, 360582165874913696, 360582166059172085, 360582166197097301, 360582166225369209, 360582166226613059, 360582166185192616, 360582166143535491, 360582166045887154]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk952A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk379A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589824297290780, 360589833106299384⟩, ⟨(-308408083288463498), (-308182409211351904)⟩, true⟩

def state01 : KState := ⟨⟨360672990384137574, 360672999197972895⟩, ⟨(-3460884758328590449), (-3460658901295410475)⟩, true⟩

def words00 : List Nat := [360581702597179553, 360581703683147778, 360581705141900728, 360581706600675015, 360581707448136021, 360581708190922555, 360581709628541109, 360581711066241980, 360581713022256439, 360581715430694390]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360637585210305920, 360637594029011617⟩, ⟨(-2118380743414949227), (-2118154701720996843)⟩, true⟩

def words01 : List Nat := [360581717489922185, 360581719549106120, 360581722019516153, 360581724918652167, 360581727641483438, 360581730364254605, 360581732550594542, 360581734044840590, 360581735518362110, 360581736991968264]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604624450779653, 360604633274304079⟩, ⟨(-868374169921088653), (-868147945477469691)⟩, true⟩

def words02 : List Nat := [360581738672425449, 360581739879879771, 360581740738711854, 360581741597555707, 360581742017728353, 360581743009599711, 360581743847093333, 360581744684642493, 360581745112807610, 360581745716752803]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360628580318598895, 360628589146956961⟩, ⟨(-1777159341406021975), (-1776932933598368061)⟩, true⟩

def words03 : List Nat := [360581746842408131, 360581747968154453, 360581749073448146, 360581749983717402, 360581750314484819, 360581750645270088, 360581751433185486, 360581752567979127, 360581753802886398, 360581755037850761]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602685620623028, 360602694453855387⟩, ⟨(-794816046761830941), (-794589454000502521)⟩, true⟩

def words04 : List Nat := [360581755924576455, 360581756356897167, 360581757084268937, 360581757811758537, 360581758363851930, 360581758364363783, 360581758225713705, 360581757525016807, 360581756824258742, 360581757207037109]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk379A

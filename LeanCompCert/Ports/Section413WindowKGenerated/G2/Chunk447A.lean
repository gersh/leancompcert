import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk447A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360547208183788905, 360547220603745623⟩, ⟨1607097684006204133, 1607472855479421573⟩, true⟩

def state01 : KState := ⟨⟨360564178576496100, 360564191002218065⟩, ⟨848518876892988807, 848894306102079505⟩, true⟩

def words00 : List Nat := [360583181161173379, 360583180857285971, 360583180708542442, 360583180307826027, 360583179907023767, 360583179378643000, 360583179103267378, 360583178757444849, 360583178411580408, 360583177678713303]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360611298324637961, 360611310756132190⟩, ⟨(-1258480888431810084), (-1258105201116508150)⟩, true⟩

def words01 : List Nat := [360583177329675393, 360583177405474473, 360583177826577312, 360583177888505432, 360583177889073092, 360583177455167621, 360583177021154005, 360583177183116336, 360583177812715922, 360583178442429087]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360614456724736596, 360614469162068856⟩, ⟨(-1400000770055627091), (-1399624821635428285)⟩, true⟩

def words02 : List Nat := [360583178820392049, 360583178882999206, 360583178933901888, 360583178984972972, 360583178985485602, 360583178979723266, 360583178980269691, 360583178702125097, 360583178644437130, 360583179344679676]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360529994213125593, 360530006656215624⟩, ⟨2378561563038236145, 2378937769032843197⟩, true⟩

def words03 : List Nat := [360583180338063636, 360583181331520300, 360583181936056857, 360583182041866253, 360583182042379206, 360583181883640130, 360583181724741019, 360583181285124565, 360583180346747204, 360583179158876171]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589157624643440, 360589170073512800⟩, ⟨(-268664969392569147), (-268288504802711257)⟩, true⟩

def words04 : List Nat := [360583177970919704, 360583177282224367, 360583176846254231, 360583176776807578, 360583176707305124, 360583176209990474, 360583175567954013, 360583175191382805, 360583174814638411, 360583174933632067]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk447A

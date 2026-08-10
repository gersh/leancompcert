import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk513A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580164992806275, 360580181537057691⟩, ⟨90381277755516216, 90954751481364682⟩, true⟩

def state01 : KState := ⟨⟨360584538752894751, 360584555303832630⟩, ⟨(-134144508885658479), (-133570692110660041)⟩, true⟩

def words00 : List Nat := [360581954588614064, 360581954589323470, 360581954397742540, 360581953904214834, 360581953410586191, 360581952747069249, 360581952347181545, 360581952326390417, 360581952305528407, 360581952144819735]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565942752752147, 360565959310382464⟩, ⟨820098145432810099, 820672305630547731⟩, true⟩

def words01 : List Nat := [360581952309324285, 360581952474027752, 360581952747871956, 360581952748581448, 360581952643538459, 360581952164895857, 360581951686145963, 360581951197904006, 360581950897668574, 360581950586797713]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569639073490722, 360569655637879043⟩, ⟨630172179534793205, 630746686585631467⟩, true⟩

def words02 : List Nat := [360581950275836623, 360581949775048015, 360581949018795639, 360581948391396148, 360581947763816425, 360581947035271224, 360581946252671676, 360581945278532546, 360581944304295469, 360581943708921039]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360522794699883846, 360522811270966725⟩, ⟨3034918682881342737, 3035493533596979021⟩, true⟩

def words03 : List Nat := [360581943470115901, 360581943221836306, 360581942973488634, 360581942499017280, 360581941645827349, 360581940698326973, 360581939750653071, 360581938673435854, 360581937734196792, 360581936583268965]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585163431829753, 360585180009610091⟩, ⟨(-167410801465794902), (-166835606869635418)⟩, true⟩

def words04 : List Nat := [360581935432223151, 360581934659865973, 360581934103806612, 360581933926325545, 360581933748813457, 360581933203187556, 360581932278927056, 360581931733292444, 360581931187465649, 360581931083457346]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk513A

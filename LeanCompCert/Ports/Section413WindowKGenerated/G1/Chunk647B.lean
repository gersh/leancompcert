import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk647A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk647B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk647A

def state06 : KState := ⟨⟨362482461255504028, 362482523117621256⟩, ⟨193043082951949891, 195748955742254661⟩, true⟩

def words05 : List Nat := [371285546216259176, 371285546343971451, 371285546571964146, 371285546574167701, 371285546484665864, 371285546355201297, 371285546224902395, 371285546088853399, 371285545844873799, 371285545800693249]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481335312990729, 362481397195007596⟩, ⟨265903824598864594, 268610986187978134⟩, true⟩

def words06 : List Nat := [371285545755666338, 371285545710874839, 371285545347760304, 371285545224116713, 371285545099341563, 371285545047978351, 371285544818612027, 371285544589754083, 371285544359955421, 371285544346253358]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469284076780565, 362469345978633615⟩, ⟨1046541858538753340, 1049250305020393452⟩, true⟩

def words07 : List Nat := [371285544285769300, 371285544290160078, 371285544294607289, 371285544296811800, 371285544005314997, 371285543785828251, 371285543565186824, 371285543561110003, 371285543359665757, 371285543112085613]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487849853919963, 362487911775496589⟩, ⟨(-156199717345109853), (-153489993069681105)⟩, true⟩

def words08 : List Nat := [371285542863552137, 371285542854108919, 371285542856823816, 371285542978911583, 371285543040438367, 371285543042645131, 371285542846828130, 371285542744175136, 371285542734867111, 371285542773736010]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486660972392313, 362486722914122806⟩, ⟨(-79117748487228664), (-76406718348062456)⟩, true⟩

def words09 : List Nat := [371285542794600415, 371285542816264035, 371285543075012052, 371285543215755877, 371285543428269255, 371285543641600619, 371285543853927921, 371285543856133448, 371285543795302596, 371285543816294871]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk647B

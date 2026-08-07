import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk323

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360521402735412054, 360521409049749676⟩, ⟨1943875242304442223, 1944013153684610059⟩, true⟩

def state01 : KState := ⟨⟨360503588805878667, 360503595124315913⟩, ⟨2519079530305879869, 2519217574123925571⟩, true⟩

def words00 : List Nat := [360581593352594571, 360581590795367638, 360581587696681122, 360581585552841826, 360581583409029531, 360581580429849539, 360581576977439222, 360581572778997764, 360581568580733794, 360581565337071219]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360469159642604061, 360469165965102712⟩, ⟨3631740158070817951, 3631878333132926343⟩, true⟩

def words01 : List Nat := [360581562924302881, 360581561202214960, 360581559480179346, 360581557280042245, 360581554415722022, 360581551046079656, 360581547676520897, 360581544626072544, 360581541914814345, 360581538438281330]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571107742422962, 360571114068982784⟩, ⟨336345109712321395, 336483416052365205⟩, true⟩

def words02 : List Nat := [360581534961866224, 360581532439226171, 360581530402750148, 360581529319857691, 360581528236999062, 360581526330942181, 360581524457421668, 360581523537345902, 360581522617199114, 360581521845538688]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561474888274099, 360561481218944785⟩, ⟨647666720508869830, 647805159772487146⟩, true⟩

def words03 : List Nat := [360581521524011050, 360581520589335319, 360581519654641297, 360581518429290684, 360581517867520838, 360581516815880106, 360581515764260665, 360581514231299776, 360581512918858527, 360581512299951974]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360552163759679064, 360552170094403154⟩, ⟨948889733107105520, 949028303478611004⟩, true⟩

def words04 : List Nat := [360581512014055238, 360581512014486262, 360581511710219368, 360581510928372517, 360581510146501768, 360581509124266478, 360581508606097909, 360581508062777808, 360581507519444468, 360581506363444224]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360587026182821652, 360587032521613273⟩, ⟨(-179224185831663261), (-179085483854621945)⟩, true⟩

def words05 : List Nat := [360581505456984393, 360581504207728215, 360581502958423248, 360581502661045285, 360581502395419881, 360581501314403729, 360581500233374428, 360581498968289044, 360581498359119661, 360581498530579170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589287642504859, 360589293985410858⟩, ⟨(-252669795801194892), (-252530960663107570)⟩, true⟩

def words06 : List Nat := [360581498530970630, 360581497855135110, 360581497199383356, 360581497347481375, 360581497347842444, 360581497255747831, 360581496210624020, 360581494688844978, 360581493167069014, 360581492837449316]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360522156161810078, 360522162508774560⟩, ⟨1920864579298663330, 1921003545830550630⟩, true⟩

def words07 : List Nat := [360581494029642189, 360581495221843894, 360581495697469359, 360581495697900823, 360581495220906768, 360581493977225443, 360581492733493751, 360581492440487387, 360581491195002473, 360581489363185634]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360552057971453117, 360552064322497961⟩, ⟨952591134203523697, 952730232877371989⟩, true⟩

def words08 : List Nat := [360581487531384528, 360581486650268427, 360581486521464000, 360581486297900086, 360581486074313916, 360581484923619269, 360581482820816207, 360581481443775230, 360581480066699211, 360581478655096831]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360528033626500372, 360528039981660209⟩, ⟨1730819359016709021, 1730958590995177865⟩, true⟩

def words09 : List Nat := [360581477747383121, 360581476200191594, 360581474653013420, 360581473620079017, 360581473070449766, 360581471762482334, 360581470454539102, 360581468671002720, 360581466277992538, 360581464629530431]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk323

import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk591A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk591B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk591A

def state06 : KState := ⟨⟨362499573762678845, 362499625021347771⟩, ⟨(-864886853573053856), (-862838451315107042)⟩, true⟩

def words05 : List Nat := [371285038632943683, 371285038713394303, 371285039039369376, 371285039224016050, 371285039493375918, 371285039763477242, 371285039980086444, 371285039982099994, 371285040190390508, 371285040439421923]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491083676586072, 362491134953072495⟩, ⟨(-362553429925488377), (-360503973492886111)⟩, true⟩

def words06 : List Nat := [371285040928025903, 371285041036271730, 371285041096766885, 371285041157945799, 371285041303881338, 371285041347837484, 371285041676958765, 371285042006911291, 371285042269347023, 371285042374385421]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497296638322047, 362497347932889886⟩, ⟨(-730212078826717222), (-728161552424551528)⟩, true⟩

def words07 : List Nat := [371285042578851729, 371285042784301790, 371285043227978698, 371285043291457361, 371285043307788934, 371285043324754442, 371285043483575791, 371285043538329561, 371285043747604651, 371285043957755560]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475872358931662, 362475923671530304⟩, ⟨537767357213711657, 539818950770364689⟩, true⟩

def words08 : List Nat := [371285044165845405, 371285044167846458, 371285044171327861, 371285044317775581, 371285044460095731, 371285044462096998, 371285044256562984, 371285044055467726, 371285043853591409, 371285043775446006]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463658516087687, 362463709846739406⟩, ⟨1260828131002992380, 1262880793212273910⟩, true⟩

def words09 : List Nat := [371285043622733653, 371285043615669390, 371285043607887582, 371285043601965095, 371285043304703262, 371285043093990023, 371285042954957422, 371285042956959017, 371285042650640943, 371285042292570695]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk591B

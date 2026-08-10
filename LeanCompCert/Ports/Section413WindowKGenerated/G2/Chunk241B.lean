import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk241A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk241B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk241A

def state06 : KState := ⟨⟨360596976776142276, 360596980221417627⟩, ⟨(-344723129944953498), (-344666817448094106)⟩, true⟩

def words05 : List Nat := [360582688325660012, 360582693897132783, 360582698410065729, 360582702451847375, 360582706051243258, 360582709650429595, 360582712163400892, 360582713619650233, 360582714210435909, 360582714801217797]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360648759813061727, 360648763261308576⟩, ⟨(-1596016645871793723), (-1595960261568736147)⟩, true⟩

def words06 : List Nat := [360582716354043599, 360582718760145742, 360582722340187614, 360582725919998544, 360582728043718343, 360582729146427354, 360582729738212027, 360582730330037469, 360582732633694012, 360582735365831818]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360699169076239719, 360699172527491760⟩, ⟨(-2814915639252478417), (-2814859182299427993)⟩, true⟩

def words07 : List Nat := [360582736786917996, 360582738207916073, 360582740407345820, 360582743845404022, 360582746819621998, 360582749793644850, 360582751903623061, 360582755008273065, 360582759823148403, 360582764637731228]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360692323803817938, 360692327258034281⟩, ⟨(-2649373344311711143), (-2649316815666711213)⟩, true⟩

def words08 : List Nat := [360582771162218298, 360582776476231914, 360582780927248760, 360582785377929245, 360582788666235732, 360582793034106341, 360582797821035434, 360582802607628241, 360582806099557220, 360582810627234947]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360707399938134358, 360707403395332295⟩, ⟨(-3014263669292265584), (-3014207068507605958)⟩, true⟩

def words09 : List Nat := [360582815683362205, 360582820739172159, 360582826275246212, 360582830116630212, 360582832517246625, 360582834917689677, 360582839026185676, 360582844236575845, 360582849383908140, 360582854530884231]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk241B

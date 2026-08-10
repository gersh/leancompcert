import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk621A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk621B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk621A

def state06 : KState := ⟨⟨362490997301923258, 362491054113274406⟩, ⟨(-353592186521394589), (-351206883969343457)⟩, true⟩

def words05 : List Nat := [371285402779310812, 371285402996033403, 371285403279777935, 371285403435934595, 371285403656355303, 371285403877557412, 371285404096963572, 371285404099072762, 371285404064189824, 371285404157772253]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469160924286301, 362469217754401344⟩, ⟨1003890815337942093, 1006277284352963771⟩, true⟩

def words06 : List Nat := [371285404381562395, 371285404383671657, 371285404262627460, 371285404143282729, 371285404023153240, 371285403981855626, 371285403841772391, 371285403794378501, 371285403746257239, 371285403652492915]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500141930525440, 362500198779692161⟩, ⟨(-922321535792773905), (-919933882239988045)⟩, true⟩

def words07 : List Nat := [371285403393579153, 371285403394753885, 371285403624181862, 371285403641138052, 371285403642772505, 371285403616902908, 371285403776482338, 371285403847033410, 371285404086408635, 371285404326688189]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487322462483859, 362487379330718919⟩, ⟨(-125236645031784184), (-122847805711573478)⟩, true⟩

def words08 : List Nat := [371285404511724870, 371285404513834899, 371285404353942115, 371285404326642442, 371285404346429714, 371285404348547652, 371285404191447187, 371285404030960598, 371285403965599320, 371285403999791429]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479857166932116, 362479914054172513⟩, ⟨339156528422051123, 341546549779405671⟩, true⟩

def words09 : List Nat := [371285404291761853, 371285404584623465, 371285404875684667, 371285404941193894, 371285405019905013, 371285405099608684, 371285405327822674, 371285405329933317, 371285405242149023, 371285405156258999]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk621B

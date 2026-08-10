import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk655A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk655B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk655A

def state06 : KState := ⟨⟨362476126688899444, 362476190150191414⟩, ⟨607502176599045233, 610312253151360315⟩, true⟩

def words05 : List Nat := [371285499141238829, 371285499362066512, 371285499582075598, 371285499584309445, 371285499528730292, 371285499485049956, 371285499626341961, 371285499628575632, 371285499506438622, 371285499366987500]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481985990101353, 362482049471398884⟩, ⟨223438686938164352, 226250075155678172⟩, true⟩

def words06 : List Nat := [371285499283683477, 371285499286188329, 371285499467982022, 371285499676738432, 371285499860565617, 371285499862799396, 371285499820518671, 371285499907215629, 371285499981136548, 371285499983449451]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480241427762729, 362480304929379914⟩, ⟨337839368550377767, 340652089232768681⟩, true⟩

def words07 : List Nat := [371285499932508370, 371285499835854331, 371285499807884790, 371285499810369515, 371285499765654250, 371285499766374461, 371285499766278378, 371285499766735451, 371285499456735241, 371285499380267880]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484115940558840, 362484179462106339⟩, ⟨83750697537015656, 86564725353804264⟩, true⟩

def words08 : List Nat := [371285499455662905, 371285499457912385, 371285499411648254, 371285499313348542, 371285499214174766, 371285499157312241, 371285499083827007, 371285499164864449, 371285499245167728, 371285499247521095]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497386215954587, 362497449757720192⟩, ⟨(-786729253050610655), (-783913899029264907)⟩, true⟩

def words09 : List Nat := [371285499416997054, 371285499607791304, 371285499878726592, 371285499880961368, 371285499842489724, 371285499767920950, 371285499712015602, 371285499714492080, 371285499848175520, 371285500032883235]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk655B

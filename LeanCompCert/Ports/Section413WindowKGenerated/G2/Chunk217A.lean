import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk217A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360548685253102320, 360548688006111291⟩, ⟨681117775273396217, 681158197498605257⟩, true⟩

def state01 : KState := ⟨⟨360577940764566533, 360577943520217616⟩, ⟨46250218409900804, 46290697982378558⟩, true⟩

def words00 : List Nat := [360580077007858836, 360580078744505965, 360580080775608620, 360580082806576082, 360580083011155796, 360580083011435949, 360580081105349556, 360580079093682478, 360580077082116620, 360580075749512060]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569971509511606, 360569974267829640⟩, ⟨219441869440932672, 219482406925914800⟩, true⟩

def words01 : List Nat := [360580075651552025, 360580074489795601, 360580074279373917, 360580077213956857, 360580079069525901, 360580080924969731, 360580081424738480, 360580081425018813, 360580079815966926, 360580079351021441]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360527272242662521, 360527275003624635⟩, ⟨1146656842467418286, 1146697437394861562⟩, true⟩

def words02 : List Nat := [360580078886030564, 360580077645126143, 360580074295943690, 360580069558083213, 360580064820615074, 360580058587958122, 360580053935116948, 360580051393606560, 360580048852294705, 360580045249247961]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360610193501102129, 360610196264711069⟩, ⟨(-655854461322654102), (-655813808866529848)⟩, true⟩

def words03 : List Nat := [360580042821135629, 360580041628694067, 360580040739199826, 360580040739480387, 360580038935901482, 360580035043653221, 360580031151705871, 360580029368769246, 360580030035862090, 360580031423679538]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360546470477269917, 360546473243553934⟩, ⟨729726163152605565, 729766873778209267⟩, true⟩

def words04 : List Nat := [360580031751068684, 360580032149852087, 360580033228223999, 360580034306580745, 360580034849945990, 360580034850226697, 360580034003210134, 360580031567635527, 360580029132236303, 360580025743497760]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk217A

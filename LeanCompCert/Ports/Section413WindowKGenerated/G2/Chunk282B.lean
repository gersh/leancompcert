import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk282A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk282B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk282A

def state06 : KState := ⟨⟨360528771006293517, 360528775785068285⟩, ⟨1513884624777728998, 1513975965197087830⟩, true⟩

def words05 : List Nat := [360582353324234552, 360582352479696367, 360582351635141127, 360582351891410458, 360582352138695339, 360582352386023441, 360582352386355597, 360582352007124884, 360582350786062164, 360582348890701587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563581577281179, 360563586359566416⟩, ⟨529887126323572144, 529978565966740862⟩, true⟩

def words06 : List Nat := [360582346995348311, 360582345920722169, 360582344493764723, 360582342440951216, 360582340388222278, 360582338015905431, 360582336598840824, 360582335750638172, 360582334902458107, 360582333390552152]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608696747640684, 360608701533449932⟩, ⟨(-745988858271233394), (-745897318986944722)⟩, true⟩

def words07 : List Nat := [360582332727735910, 360582332485700525, 360582332243577456, 360582331926632536, 360582330806070364, 360582328614471676, 360582326422956791, 360582325478151731, 360582326097449673, 360582327030462522]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591770381087051, 360591775170446677⟩, ⟨(-267561826741699748), (-267470187034851446)⟩, true⟩

def words08 : List Nat := [360582327030797066, 360582327006106765, 360582326519217612, 360582326899112137, 360582326959557332, 360582326959930421, 360582325777175502, 360582323631509623, 360582321485921504, 360582320920436609]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575095219557545, 360575100012429469⟩, ⟨204404955134159009, 204496694221785591⟩, true⟩

def words09 : List Nat := [360582321788280089, 360582322656135363, 360582322899445418, 360582323584841690, 360582323951516513, 360582324318268180, 360582325929678286, 360582326298654091, 360582326298986622, 360582326044027412]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk282B

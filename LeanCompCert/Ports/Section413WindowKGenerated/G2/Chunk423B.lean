import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk423A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk423B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk423A

def state06 : KState := ⟨⟨360570779416707483, 360570790521196975⟩, ⟨498872799524902105, 499190693844585861⟩, true⟩

def words05 : List Nat := [360582576250328904, 360582575960393785, 360582575707262343, 360582576095303540, 360582576245570388, 360582576395923993, 360582576396446677, 360582576116174273, 360582575281601942, 360582575004054496]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555886021072662, 360555897130994266⟩, ⟨1129741930345016347, 1130060054795801931⟩, true⟩

def words06 : List Nat := [360582574726332299, 360582574532884983, 360582573987174624, 360582573155369093, 360582572323497580, 360582571210971489, 360582570462877732, 360582569875746799, 360582569288581110, 360582568361931151]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591887679720281, 360591898795095948⟩, ⟨(-395984986094527773), (-395666630528718683)⟩, true⟩

def words07 : List Nat := [360582567732936817, 360582567088909002, 360582566444732513, 360582566357118484, 360582565715599712, 360582564615956567, 360582563516255308, 360582562745701747, 360582562630490960, 360582562851382286]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360519807602549532, 360519818723421152⟩, ⟨2658957443813407066, 2659276032324450498⟩, true⟩

def words08 : List Nat := [360582562851902539, 360582562681906674, 360582561958069103, 360582561318769242, 360582560679355388, 360582559646923706, 360582558060787385, 360582556161176837, 360582554261547205, 360582552293421729]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360536440408152996, 360536451534468953⟩, ⟨1953889437139247222, 1954208256462816460⟩, true⟩

def words09 : List Nat := [360582550814009061, 360582549890781803, 360582548967527640, 360582547694257501, 360582546584216087, 360582545237622437, 360582543890923301, 360582543100304182, 360582542438289629, 360582541351838360]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk423B

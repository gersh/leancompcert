import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk451A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk451B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk451A

def state06 : KState := ⟨⟨360511167726629470, 360511180414182995⟩, ⟨3253465458621680194, 3253852653324122684⟩, true⟩

def words05 : List Nat := [360583239134781497, 360583239112848951, 360583239090853909, 360583238760751335, 360583238070420548, 360583237054598138, 360583236038648090, 360583235010730968, 360583233662138715, 360583232067268118]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556389299696688, 360556401993085735⟩, ⟨1211112592926614417, 1211500051190571697⟩, true⟩

def words06 : List Nat := [360583230472328305, 360583229367383662, 360583228576966511, 360583227999875608, 360583227422751510, 360583226430472717, 360583225369428540, 360583224490388939, 360583223611208537, 360583222893045677]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558506125618679, 360558518824908532⟩, ⟨1115407122882483393, 1115794847714493001⟩, true⟩

def words07 : List Nat := [360583222299848059, 360583221317195678, 360583220334467699, 360583219740196104, 360583219392504366, 360583218755663252, 360583218118786903, 360583217060782155, 360583216025279766, 360583215479351084]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584230671079043, 360584243376190257⟩, ⟨(-46911116360812566), (-46523128490226564)⟩, true⟩

def words08 : List Nat := [360583214933235184, 360583214901415316, 360583214901966225, 360583214681283691, 360583214460519106, 360583213902549392, 360583213831962681, 360583213976408413, 360583213976964527, 360583213898451543]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360607396506127230, 360607409217082992⟩, ⟨(-1093821722870703249), (-1093433470856602549)⟩, true⟩

def words09 : List Nat := [360583214410809903, 360583214923338499, 360583215746186624, 360583216259223525, 360583216301094174, 360583216343010411, 360583216873742406, 360583217674726111, 360583218210449533, 360583218746277997]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk451B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk817A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk817B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk817A

def state06 : KState := ⟨⟨360570243732211031, 360570287346245019⟩, ⟨977923086466529365, 980331341377023713⟩, true⟩

def words05 : List Nat := [360582276858730828, 360582277238448009, 360582277479244730, 360582277633587747, 360582277734962629, 360582277836658703, 360582277915153734, 360582277916324867, 360582277845645939, 360582277700224680]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589475781565357, 360589519406647389⟩, ⟨(-594605709398395934), (-592196551144959260)⟩, true⟩

def words06 : List Nat := [360582277557366610, 360582277636439904, 360582277737733659, 360582277839242925, 360582277840334898, 360582277801003863, 360582277612231178, 360582277419778061, 360582277226985814, 360582277272502705]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598106880615327, 360598150516850035⟩, ⟨(-1300407168510538669), (-1297997098250734157)⟩, true⟩

def words07 : List Nat := [360582277273546329, 360582277273398421, 360582277421160622, 360582277717373286, 360582277973985507, 360582278230783936, 360582278412534919, 360582278504657253, 360582278699686224, 360582278895101087]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580305754837844, 360580349402116622⟩, ⟨155408763793959784, 157819737292509278⟩, true⟩

def words08 : List Nat := [360582279086577950, 360582279167671619, 360582279168731036, 360582279152419641, 360582279135924221, 360582279022132495, 360582279014780994, 360582279034079712, 360582279035123451, 360582278974647403]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603881693134781, 360603925351470571⟩, ⟨(-1773027916428929691), (-1770616038523206895)⟩, true⟩

def words09 : List Nat := [360582279041649550, 360582279132597190, 360582279345389656, 360582279409281742, 360582279410383963, 360582279332753612, 360582279295284091, 360582279411845999, 360582279677413554, 360582279943241782]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk817B

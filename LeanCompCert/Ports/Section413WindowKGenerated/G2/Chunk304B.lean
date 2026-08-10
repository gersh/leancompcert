import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk304A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk304B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk304A

def state06 : KState := ⟨⟨360528083985983489, 360528089573668613⟩, ⟨1685597148767702965, 1685712250913452805⟩, true⟩

def words05 : List Nat := [360583429816214286, 360583431901289256, 360583433448669373, 360583433922760660, 360583434124232174, 360583434325801915, 360583434326135316, 360583434115135089, 360583433223761143, 360583431407250802]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360614790567740405, 360614796159240096⟩, ⟨(-956006736390667718), (-955891518033598028)⟩, true⟩

def words06 : List Nat := [360583429590768574, 360583428569115049, 360583428232746179, 360583428377015044, 360583428377391361, 360583427620542688, 360583425791384189, 360583425035437959, 360583424596034651, 360583425626010678]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608507150287636, 360608512745643599⟩, ⟨(-764611709479891068), (-764496373603104336)⟩, true⟩

def words07 : List Nat := [360583425813955518, 360583426001927854, 360583426823570520, 360583428185543316, 360583428893148959, 360583429600774000, 360583429772026998, 360583430019909794, 360583430843161497, 360583431666492551]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546919474652956, 360546925073817408⟩, ⟨1112672872562020319, 1112788324541022101⟩, true⟩

def words08 : List Nat := [360583432069864256, 360583432070268947, 360583431402242272, 360583430201242263, 360583429000262662, 360583426853468511, 360583425247501138, 360583424311164520, 360583423374845041, 360583421903090646]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360622412991104789, 360622418594099652⟩, ⟨(-1189472422208262581), (-1189356853422384117)⟩, true⟩

def words09 : List Nat := [360583420706447663, 360583420581191776, 360583421401216652, 360583421616966659, 360583421617340795, 360583420955724917, 360583420702994772, 360583422008100522, 360583423287010420, 360583424565922793]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk304B

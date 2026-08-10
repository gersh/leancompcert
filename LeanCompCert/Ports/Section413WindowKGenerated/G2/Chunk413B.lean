import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk413A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk413B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk413A

def state06 : KState := ⟨⟨360655469909115796, 360655480474808805⟩, ⟨(-3024595072445910707), (-3024299733277207851)⟩, true⟩

def words05 : List Nat := [360582351483741007, 360582352180915690, 360582353047205955, 360582354005143786, 360582354461398546, 360582354917679983, 360582355957020718, 360582357338942441, 360582359107364497, 360582360875832059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360628571520246756, 360628582091297880⟩, ⟨(-1912249231613141509), (-1911953670806553307)⟩, true⟩

def words06 : List Nat := [360582362230343070, 360582363003341986, 360582363564600686, 360582364125994211, 360582364538345082, 360582365074539553, 360582365318453856, 360582365562417584, 360582366145013849, 360582367262775327]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564028457717117, 360564039034058547⟩, ⟨758294936491213612, 758590716185041700⟩, true⟩

def words07 : List Nat := [360582368469835952, 360582369676942693, 360582370589785718, 360582371090928109, 360582371415086348, 360582371739377040, 360582371853589305, 360582371854153030, 360582371779946705, 360582371337494629]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360630145530232166, 360630156111879011⟩, ⟨(-1977930822888377771), (-1977634823630256759)⟩, true⟩

def words08 : List Nat := [360582371034456939, 360582371647853301, 360582372565300899, 360582373482820985, 360582373907665745, 360582373908228146, 360582374178029607, 360582374604468835, 360582375613021269, 360582376767972601]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617022779766898, 360617033366783864⟩, ⟨(-1434861284728053916), (-1434565063174666458)⟩, true⟩

def words09 : List Nat := [360582377466374194, 360582378164792019, 360582378753607951, 360582379633954688, 360582380167600081, 360582380701310153, 360582380943120665, 360582381198642771, 360582382036106665, 360582382873723922]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk413B

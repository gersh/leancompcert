import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk673A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk673B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk673A

def state06 : KState := ⟨⟨360558774202711906, 360558803357277902⟩, ⟨1623809703563390946, 1625136263400199128⟩, true⟩

def words05 : List Nat := [360582930831905131, 360582930827904159, 360582930823809480, 360582930630347943, 360582930530177719, 360582930325731176, 360582930121002068, 360582930093926105, 360582929846642295, 360582929489454271]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568383718414998, 360568412881971083⟩, ⟨976417294457064842, 977744459910627234⟩, true⟩

def words06 : List Nat := [360582929132074864, 360582928770121770, 360582928530095830, 360582928304154573, 360582928078148636, 360582927664033424, 360582927186829557, 360582926696733959, 360582926206355771, 360582925936148175]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360544959586644086, 360544988759255631⟩, ⟨2554657357039698438, 2555985132603326604⟩, true⟩

def words07 : List Nat := [360582925721578015, 360582925353941473, 360582924986133816, 360582924784979308, 360582924715687976, 360582924445939486, 360582924176095764, 360582923761749821, 360582923205589122, 360582922643681326]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562160855913093, 360562190037492447⟩, ⟨1395547060493128113, 1396875440353264181⟩, true⟩

def words08 : List Nat := [360582922081474843, 360582921659955415, 360582921244510043, 360582920717925894, 360582920191202267, 360582919609456219, 360582919194558167, 360582918942672236, 360582918690702242, 360582918267798921]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587261450585041, 360587290641146613⟩, ⟨(-296133553472727553), (-294804568256713911)⟩, true⟩

def words09 : List Nat := [360582917960986637, 360582917874276773, 360582917795960508, 360582917796912749, 360582917675970521, 360582917367438620, 360582917058721439, 360582916774334793, 360582916685141870, 360582916751022480]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk673B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk884A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk884B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk884A

def state06 : KState := ⟨⟨360572591775203241, 360572643142601492⟩, ⟨837041609788624710, 840110118845037484⟩, true⟩

def words05 : List Nat := [360582141775378945, 360582141586001762, 360582141396208265, 360582141315079017, 360582141148541247, 360582140873781760, 360582140598784442, 360582140414174073, 360582140310805093, 360582140204763431]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587066421792809, 360587117801340432⟩, ⟨(-443546141887445882), (-440476558038142220)⟩, true⟩

def words06 : List Nat := [360582140098550911, 360582139928829564, 360582139739319479, 360582139677755181, 360582139615856104, 360582139483559634, 360582139387513516, 360582139208291214, 360582139028825128, 360582139033630809]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581262501608813, 360581313893177946⟩, ⟨69978380265040975, 73049027716646633⟩, true⟩

def words07 : List Nat := [360582139218487115, 360582139403583656, 360582139468583077, 360582139469858913, 360582139460267766, 360582139418178858, 360582139430390114, 360582139499336076, 360582139500484697, 360582139492496625]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588760198754328, 360588811602349050⟩, ⟨(-593449005998726659), (-590377294462028397)⟩, true⟩

def words08 : List Nat := [360582139535109843, 360582139651568437, 360582139824000137, 360582139996678838, 360582140042667947, 360582140043943053, 360582139989238341, 360582139931991769, 360582139917285520, 360582139993999478]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589233117945588, 360589284533677859⟩, ⟨(-635297867076638357), (-632225081428686273)⟩, true⟩

def words09 : List Nat := [360582139995140951, 360582139990884164, 360582140108326506, 360582140336682050, 360582140482118404, 360582140627752367, 360582140709704797, 360582140710980027, 360582140745990091, 360582140828166863]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk884B

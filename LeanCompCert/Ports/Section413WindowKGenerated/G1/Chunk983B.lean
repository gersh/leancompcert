import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk983A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk983B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk983A

def state06 : KState := ⟨⟨362487680044835421, 362487827447411510⟩, ⟨(-253069605572693312), (-243280979418633634)⟩, true⟩

def words05 : List Nat := [371285354156537498, 371285354166630908, 371285354260294664, 371285354263749045, 371285354219953246, 371285354165153894, 371285354109020321, 371285354097072179, 371285354070384892, 371285354099444139]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484417218250513, 362484564652028347⟩, ⟨67851691198430149, 77643386513396283⟩, true⟩

def words06 : List Nat := [371285354127166556, 371285354130654311, 371285354106506116, 371285354127844987, 371285354173036542, 371285354176491617, 371285354093926078, 371285354012407863, 371285353947495481, 371285353951474453]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474065649037420, 362474213113904421⟩, ⟨1086181063576770249, 1095975817296759453⟩, true⟩

def words07 : List Nat := [371285353946465011, 371285353950798573, 371285353953398326, 371285353936875523, 371285353791299365, 371285353677567441, 371285353562013813, 371285353551004854, 371285353453189751, 371285353343801725]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484825016163211, 362484972511954744⟩, ⟨27643409721304905, 37441205952391471⟩, true⟩

def words08 : List Nat := [371285353232908779, 371285353217529288, 371285353180949566, 371285353205160314, 371285353207880536, 371285353204204708, 371285353061721141, 371285353024382485, 371285353047110244, 371285353050687872]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480249805366516, 362480397332724772⟩, ⟨477856605127069474, 487657507358238274⟩, true⟩

def words09 : List Nat := [371285353049402715, 371285353049220333, 371285353132217073, 371285353180950073, 371285353233729578, 371285353287795136, 371285353334983093, 371285353338438965, 371285353247725310, 371285353201701990]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk983B

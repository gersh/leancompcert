import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk887A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk887B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk887A

def state06 : KState := ⟨⟨362481917001688549, 362482036087825384⟩, ⟨269942890387318842, 277079729719888082⟩, true⟩

def words05 : List Nat := [371285157934370583, 371285158007376709, 371285158120663124, 371285158123756426, 371285158079731053, 371285158002444174, 371285157923936352, 371285157890903219, 371285157792816076, 371285157761211143]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467002592440000, 362467121706472732⟩, ⟨1593783973553722867, 1600923289067101435⟩, true⟩

def words06 : List Nat := [371285157728353858, 371285157696277191, 371285157494135002, 371285157393318518, 371285157290990488, 371285157208461073, 371285156956158652, 371285156677656479, 371285156397850449, 371285156214629397]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464865535547483, 362464984677391608⟩, ⟨1783567153375145804, 1790708937846244014⟩, true⟩

def words07 : List Nat := [371285156013569725, 371285155940454670, 371285155866324082, 371285155787205905, 371285155625803874, 371285155491659911, 371285155355857163, 371285155305403969, 371285155085160519, 371285154861417811]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468953442459643, 362469072612032533⟩, ⟨1420604790657793400, 1427749037030288014⟩, true⟩

def words08 : List Nat := [371285154636377028, 371285154427756344, 371285154154460301, 371285153990258362, 371285153825075393, 371285153639050291, 371285153296117734, 371285153048495414, 371285152799241673, 371285152677772260]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471461553675792, 362471580751460496⟩, ⟨1197897771912476224, 1205044523349918602⟩, true⟩

def words09 : List Nat := [371285152498991521, 371285152306261602, 371285152112225210, 371285152046187283, 371285151915267330, 371285151776915133, 371285151637548076, 371285151498963046, 371285151221601600, 371285151072669392]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk887B

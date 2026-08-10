import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk552A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk552B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk552A

def state06 : KState := ⟨⟨362501157015836287, 362501201496793446⟩, ⟨(-900878851870205129), (-899218364813980213)⟩, true⟩

def words05 : List Nat := [371284927301782518, 371284927474132893, 371284927814020099, 371284927990650666, 371284928239123210, 371284928488313865, 371284928729285117, 371284928731176436, 371284928994223524, 371284929290991634]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484246448472720, 362484290945978922⟩, ⟨33725577860382713, 35386979502421021⟩, true⟩

def words06 : List Nat := [371284929879852940, 371284930033197793, 371284930190607190, 371284930348670950, 371284930521551456, 371284930545885020, 371284930773639375, 371284931002121688, 371284931200604138, 371284931202528632]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500130223088073, 362500174737452543⟩, ⟨(-844214724823570952), (-842552391343084946)⟩, true⟩

def words07 : List Nat := [371284931423647801, 371284931657359002, 371284932164479954, 371284932318087188, 371284932360117265, 371284932402705097, 371284932731666145, 371284932917246978, 371284933194251399, 371284933472074872]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362496940257006374, 362496984788137093⟩, ⟨(-667915748430988404), (-666252488025660836)⟩, true⟩

def words08 : List Nat := [371284933749690050, 371284933751549853, 371284933776974907, 371284933922947041, 371284934167657647, 371284934232400416, 371284934296022709, 371284934360273396, 371284934641535996, 371284934861602474]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480902757231743, 362480947305121000⟩, ⟨218962313880446437, 220626500947469925⟩, true⟩

def words09 : List Nat := [371284935407524204, 371284935954168290, 371284936433641890, 371284936477987762, 371284936621426162, 371284936765828889, 371284937073871104, 371284937075732351, 371284937004469074, 371284936934432890]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk552B

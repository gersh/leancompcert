import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk916A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk916B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk916A

def state06 : KState := ⟨⟨362472809603715845, 362472936913962050⟩, ⟨1107604939179757045, 1115483745195753045⟩, true⟩

def words05 : List Nat := [371285107397382651, 371285107415348333, 371285107423134948, 371285107426337617, 371285107275356823, 371285107139706504, 371285107002324155, 371285106972025487, 371285106841826495, 371285106712622270]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472695807638519, 362472823146526669⟩, ⟨1118057036221260981, 1125938467705502275⟩, true⟩

def words06 : List Nat := [371285106582024855, 371285106556434346, 371285106470152371, 371285106419493408, 371285106367856107, 371285106277252974, 371285106027040750, 371285105878997059, 371285105729332053, 371285105664991876]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475198120299990, 362475325488462718⟩, ⟨888690307405087757, 896574422634216051⟩, true⟩

def words07 : List Nat := [371285105533401340, 371285105402810160, 371285105270828097, 371285105259182125, 371285105205600831, 371285105182160411, 371285105157648168, 371285105133777277, 371285104980541530, 371285104877889357]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467282620305187, 362467410016977281⟩, ⟨1614415779644361536, 1622302508760388264⟩, true⟩

def words08 : List Nat := [371285104773400038, 371285104744786118, 371285104556864515, 371285104359148395, 371285104160253579, 371285103968665800, 371285103734046729, 371285103609864122, 371285103484584442, 371285103358767666]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486255871766419, 362486383297426243⟩, ⟨(-125345534096705984), (-117456146954342774)⟩, true⟩

def words09 : List Nat := [371285103167973347, 371285103097720149, 371285103025839734, 371285103004506434, 371285102866321017, 371285102710235920, 371285102552784511, 371285102496846482, 371285102419776888, 371285102437381595]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk916B

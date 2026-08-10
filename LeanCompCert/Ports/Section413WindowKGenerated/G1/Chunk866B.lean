import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk866A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk866B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk866A

def state06 : KState := ⟨⟨362487296616638627, 362487409924963415⟩, ⟨(-197887026411390287), (-191256985550916371)⟩, true⟩

def words05 : List Nat := [371285203575632573, 371285203529622184, 371285203487591857, 371285203490607696, 371285203344429323, 371285203183016802, 371285203020337259, 371285202985572008, 371285202940406610, 371285202969290726]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475119874843081, 362475233210354325⟩, ⟨857389125386356470, 864021522363744732⟩, true⟩

def words06 : List Nat := [371285202997077223, 371285203000092014, 371285202850215693, 371285202823228533, 371285202804910894, 371285202807934022, 371285202684169089, 371285202535624337, 371285202385895633, 371285202306031766]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475242000364587, 362475355363043813⟩, ⟨846828483363370967, 853463235128125437⟩, true⟩

def words07 : List Nat := [371285202193064300, 371285202148895347, 371285202103669163, 371285202053281062, 371285201907265335, 371285201802059773, 371285201719505817, 371285201722527762, 371285201611120516, 371285201500966381]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475312995303392, 362475426385017735⟩, ⟨840665235873454692, 847302331175796680⟩, true⟩

def words08 : List Nat := [371285201389459221, 371285201301894791, 371285201146552085, 371285201076668950, 371285201005859762, 371285200914028582, 371285200659626643, 371285200502528401, 371285200343725367, 371285200318933710]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475353300428086, 362475466717554744⟩, ⟨837171835018641905, 843811306833986729⟩, true⟩

def words09 : List Nat := [371285200208460042, 371285200062937817, 371285199916218263, 371285199903701635, 371285199823526816, 371285199751255327, 371285199677978814, 371285199602295799, 371285199367118762, 371285199258579358]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk866B

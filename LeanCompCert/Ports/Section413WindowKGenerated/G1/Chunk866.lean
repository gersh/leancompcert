import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk866

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488591977780583, 362488705123229651⟩, ⟨(-309824358819475475), (-303208427898542685)⟩, true⟩

def state01 : KState := ⟨⟨362485037079250006, 362485150251866001⟩, ⟨(-1987045557890367), 4631238161422323⟩, true⟩

def words00 : List Nat := [371285203954420411, 371285203957441179, 371285203890955003, 371285203894493900, 371285203937220076, 371285203940247057, 371285203855689686, 371285203772227295, 371285203720755093, 371285203724192077]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483874714270835, 362483987914022882⟩, ⟨98705448576682166, 105326082686821488⟩, true⟩

def words01 : List Nat := [371285203780143042, 371285203837874602, 371285203894764480, 371285203897800355, 371285203861119343, 371285203836827285, 371285203886632012, 371285203889702149, 371285203880402009, 371285203869722338]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487642246925390, 362487755473612569⟩, ⟨(-227655149407794782), (-221032182036525878)⟩, true⟩

def words02 : List Nat := [371285203910880337, 371285203914201126, 371285203977738530, 371285204056005014, 371285204084101733, 371285204087115175, 371285203937246494, 371285203922053131, 371285204019701594, 371285204052273366]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482679243772028, 362482792498000505⟩, ⟨202347407227460650, 208972760632976498⟩, true⟩

def words03 : List Nat := [371285204073411573, 371285204095678006, 371285204218019292, 371285204275059454, 371285204371637384, 371285204469363071, 371285204566215016, 371285204569228728, 371285204488360076, 371285204464305134]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470344499438124, 362470457780492745⟩, ⟨1271110039772790804, 1277737717537947706⟩, true⟩

def words04 : List Nat := [371285204506286491, 371285204509300286, 371285204401822731, 371285204294227856, 371285204185520495, 371285204098698004, 371285203961910953, 371285203894815944, 371285203826683354, 371285203743764966]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk866

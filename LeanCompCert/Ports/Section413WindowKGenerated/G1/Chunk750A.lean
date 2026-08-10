import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk750A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487390778889238, 362487474708010066⟩, ⟨(-170916265863335587), (-166665381830820115)⟩, true⟩

def state01 : KState := ⟨⟨362478295381182058, 362478379333284303⟩, ⟨511298277924331437, 515550885682803975⟩, true⟩

def words00 : List Nat := [371285252724533841, 371285252727114640, 371285252682426046, 371285252626271283, 371285252569176848, 371285252521317425, 371285252409303639, 371285252435727729, 371285252437670075, 371285252428680688]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497244357765090, 362497328333187351⟩, ⟨(-910127109745846347), (-905872752636091753)⟩, true⟩

def words01 : List Nat := [371285252424710914, 371285252513737774, 371285252778919326, 371285252808139551, 371285252810259937, 371285252813188665, 371285252992554303, 371285253084201172, 371285253246943417, 371285253410797140]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489311792554839, 362489395791259531⟩, ⟨(-315064383461817260), (-310808279585701620)⟩, true⟩

def words02 : List Nat := [371285253550257888, 371285253552839454, 371285253455382610, 371285253445146536, 371285253474320347, 371285253476950899, 371285253400743762, 371285253320906681, 371285253334899461, 371285253393056313]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475297720602562, 362475381742619281⟩, ⟨736487167672380206, 740745020764272620⟩, true⟩

def words03 : List Nat := [371285253505808037, 371285253619615500, 371285253693754549, 371285253696336730, 371285253533628216, 371285253409367895, 371285253333892175, 371285253336481503, 371285253206743008, 371285253078183837]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480229731092639, 362480313776207035⟩, ⟨366441378826888172, 370700965285073728⟩, true⟩

def words04 : List Nat := [371285252994272123, 371285252997163839, 371285253119369526, 371285253258763400, 371285253368836193, 371285253371418793, 371285253261382162, 371285253204411683, 371285253160137048, 371285253162819761]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk750A

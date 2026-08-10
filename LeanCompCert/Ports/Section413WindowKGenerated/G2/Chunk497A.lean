import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk497A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589740158165834, 360589755646349456⟩, ⟨(-391280717949533789), (-390760580430332429)⟩, true⟩

def state01 : KState := ⟨⟨360557970853185223, 360557986347893950⟩, ⟨1187675212254001262, 1188195674103492618⟩, true⟩

def words00 : List Nat := [360581893419229872, 360581893376071452, 360581892928897108, 360581892670822543, 360581892412575295, 360581892054333874, 360581891486495429, 360581890602295721, 360581889718001983, 360581888896155940]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360548929151285431, 360548944652450197⟩, ⟨1637316645209083689, 1637837428020557073⟩, true⟩

def words01 : List Nat := [360581888415880313, 360581888339237828, 360581888262520421, 360581887948124321, 360581887767448814, 360581887408876765, 360581887050111234, 360581886993766221, 360581886533672284, 360581885871839187]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586763193895914, 360586778701542971⟩, ⟨(-244066071359026283), (-243544966216610905)⟩, true⟩

def words02 : List Nat := [360581885209882218, 360581884539330049, 360581884072497574, 360581883780917676, 360581883489306815, 360581882827923950, 360581882070019325, 360581881715562898, 360581881360906317, 360581881455032412]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579241644324823, 360579257158500459⟩, ⟨129950224810832201, 130471654652071111⟩, true⟩

def words03 : List Nat := [360581881455647693, 360581881237606440, 360581881036429461, 360581881265168654, 360581881265753487, 360581881171533491, 360581881077242522, 360581880738749272, 360581880283527940, 360581880231573481]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360621414297443028, 360621429818088027⟩, ⟨(-1967823825299191302), (-1967302073639580902)⟩, true⟩

def words04 : List Nat := [360581880529666065, 360581881250436217, 360581881767871041, 360581882285354387, 360581882702750512, 360581883323849433, 360581884347632723, 360581885371506281, 360581886057102651, 360581886852647341]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk497A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk562A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552167704413474, 360552187707669442⟩, ⟨1663976917254703540, 1664736450990098330⟩, true⟩

def state01 : KState := ⟨⟨360594569276133590, 360594589286786591⟩, ⟨(-719306399233271156), (-718546449749481886)⟩, true⟩

def words00 : List Nat := [360581808826271780, 360581808502251174, 360581808439746397, 360581808242969052, 360581808046144483, 360581807579521734, 360581806877799721, 360581806492383251, 360581806106750997, 360581806264784679]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575306189993098, 360575326208094043⟩, ⟨363614850657809461, 364375218827665387⟩, true⟩

def words01 : List Nat := [360581806294982894, 360581806325270273, 360581806577253012, 360581806999217608, 360581807340673940, 360581807682245850, 360581807779012309, 360581807779795214, 360581807560815317, 360581807446422533]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360549867516603078, 360549887542072376⟩, ⟨1793793441468471404, 1794554223925315650⟩, true⟩

def words02 : List Nat := [360581807331779747, 360581807130147076, 360581806612796982, 360581805936709456, 360581805260508586, 360581804402347638, 360581803702729364, 360581803213160623, 360581802723523899, 360581802075665215]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579197671824708, 360579217704702566⟩, ⟨144251603596152085, 145012802671184035⟩, true⟩

def words03 : List Nat := [360581801508748729, 360581800838502901, 360581800168037539, 360581799715465663, 360581799078404578, 360581798138497725, 360581797198472273, 360581796574432064, 360581796213512404, 360581796168476947]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360554829799693209, 360554849840028190⟩, ⟨1514644051728410738, 1515405670228877082⟩, true⟩

def words04 : List Nat := [360581796123335185, 360581795917757046, 360581795496273144, 360581795123204575, 360581794749952847, 360581794161033459, 360581793256743680, 360581792194367163, 360581791131878292, 360581790385276704]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk562A

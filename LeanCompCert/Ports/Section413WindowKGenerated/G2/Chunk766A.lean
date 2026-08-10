import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk766A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569463601370438, 360569501689305570⟩, ⟨970021002175420277, 971991535639362273⟩, true⟩

def state01 : KState := ⟨⟨360582670320357533, 360582708418619783⟩, ⟨(-41681895607263184), (-39710571035324654)⟩, true⟩

def words00 : List Nat := [360582190709089939, 360582190500152693, 360582190488721351, 360582190568736604, 360582190569743872, 360582190504531429, 360582190269091919, 360582190204151182, 360582190138861142, 360582190078289605]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567950877881711, 360567988986533485⟩, ⟨1086056533677648167, 1088028654243451341⟩, true⟩

def words01 : List Nat := [360582190079262746, 360582190001915258, 360582189924945868, 360582190012829580, 360582190013766005, 360582189949483443, 360582189885092431, 360582189734676559, 360582189492397302, 360582189308306436]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579962224121341, 360580000343079216⟩, ⟨165736925714338838, 167709835983262336⟩, true⟩

def words02 : List Nat := [360582189123857651, 360582189107735485, 360582189108708809, 360582189053048672, 360582188997213025, 360582188931405409, 360582188973626405, 360582189016053110, 360582189017043996, 360582188909384623]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599798059512959, 360599836188782007⟩, ⟨(-1354391934714144831), (-1352418234250087101)⟩, true⟩

def words03 : List Nat := [360582189023166929, 360582189165826926, 360582189451802406, 360582189568062250, 360582189569084324, 360582189534189240, 360582189499067891, 360582189580806423, 360582189811943071, 360582190043321352]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586762412054898, 360586800551748006⟩, ⟨(-355438496339410817), (-353463996925482465)⟩, true⟩

def words04 : List Nat := [360582190170263914, 360582190171356626, 360582190128323635, 360582190081710482, 360582190034797770, 360582189945375833, 360582189782611798, 360582189514880432, 360582189246934042, 360582189209470339]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk766A

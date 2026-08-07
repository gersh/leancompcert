import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk766

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

def state06 : KState := ⟨⟨360546352593669529, 360546390743642888⟩, ⟨2742286683668897445, 2744261971117213733⟩, true⟩

def words05 : List Nat := [360582189440437354, 360582189671607623, 360582189778463759, 360582189779556588, 360582189716493577, 360582189611054100, 360582189505312451, 360582189359479663, 360582189043703972, 360582188577860436]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575344619790478, 360575382780083767⟩, ⟨519551260246403503, 521527338870963687⟩, true⟩

def words06 : List Nat := [360582188111785611, 360582187697303285, 360582187367213287, 360582187141126916, 360582186914944251, 360582186546973203, 360582186008993327, 360582185641191909, 360582185273079738, 360582185014841443]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360588770808841225, 360588808979563461⟩, ⟨(-509945901962040741), (-507969023698644189)⟩, true⟩

def words07 : List Nat := [360582184927122021, 360582184708070393, 360582184488815180, 360582184498147201, 360582184513824797, 360582184529680120, 360582184530654468, 360582184443608392, 360582184447477918, 360582184535128743]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569583277071429, 360569621458084110⟩, ⟨961434885444612281, 963412552832570407⟩, true⟩

def words08 : List Nat := [360582184649236047, 360582184683905724, 360582184684879959, 360582184634532702, 360582184584022410, 360582184415022581, 360582184330965605, 360582184211115605, 360582184091158752, 360582183885425779]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589779063653717, 360589817255004582⟩, ⟨(-587476231495716573), (-585497771222223349)⟩, true⟩

def words09 : List Nat := [360582183722504303, 360582183676285838, 360582183725170768, 360582183726265101, 360582183721270783, 360582183571484996, 360582183440335842, 360582183544948698, 360582183645375123, 360582183746038308]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk766

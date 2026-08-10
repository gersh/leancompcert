import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk800A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360615200534631228, 360615242220527870⟩, ⟨(-2648203799003362951), (-2645951498313593885)⟩, true⟩

def state01 : KState := ⟨⟨360603448013277549, 360603489710098418⟩, ⟨(-1708033825115869416), (-1705780650435771934)⟩, true⟩

def words00 : List Nat := [360582168576785638, 360582168945624879, 360582169234025167, 360582169522731942, 360582169772149177, 360582169899445937, 360582169948424577, 360582169997526857, 360582170115576793, 360582170383375396]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561833428230169, 360561875135821257⟩, ⟨1621827941432747200, 1624081977892881018⟩, true⟩

def words01 : List Nat := [360582170664098006, 360582170945031274, 360582171136767547, 360582171304766546, 360582171386293296, 360582171468116790, 360582171480879560, 360582171482023893, 360582171339011790, 360582171086557235]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587660628789459, 360587702347183963⟩, ⟨(-444983463532076270), (-442728562531316174)⟩, true⟩

def words02 : List Nat := [360582170833849638, 360582170737451318, 360582170798662520, 360582170879703495, 360582170880767510, 360582170797167721, 360582170557516681, 360582170434907718, 360582170313479481, 360582170383788138]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596314134390647, 360596355863697124⟩, ⟨(-1137623694595184673), (-1135367920255817567)⟩, true⟩

def words03 : List Nat := [360582170384826322, 360582170317602611, 360582170306944677, 360582170443016263, 360582170539833633, 360582170636846127, 360582170655225219, 360582170677736813, 360582170855888429, 360582171034418932]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573869417951265, 360573911158031554⟩, ⟨658935988895551410, 661192625626278116⟩, true⟩

def words04 : List Nat := [360582171209618919, 360582171292115188, 360582171296376738, 360582171300762907, 360582171301737704, 360582171198824345, 360582171174172904, 360582171110007765, 360582171045719562, 360582170903510958]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk800A

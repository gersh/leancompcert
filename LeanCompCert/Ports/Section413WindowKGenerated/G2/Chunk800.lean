import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk800

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

def state06 : KState := ⟨⟨360594476976723269, 360594518727625670⟩, ⟨(-990796919439664628), (-988539416344895316)⟩, true⟩

def words05 : List Nat := [360582170853917796, 360582170907862290, 360582171005835908, 360582171058408091, 360582171059474984, 360582170975506640, 360582170929735442, 360582171089176176, 360582171244347755, 360582171399758858]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581018128237756, 360581059890046176⟩, ⟨86687829408799070, 88946205692139560⟩, true⟩

def words06 : List Nat := [360582171476950356, 360582171478095279, 360582171399505636, 360582171357668676, 360582171315517642, 360582171209166320, 360582171176287146, 360582171044096008, 360582170911695458, 360582170745618702]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560972651242847, 360561014423849274⟩, ⟨1691882319661642392, 1694141560595196156⟩, true⟩

def words07 : List Nat := [360582170874564028, 360582171017598482, 360582171028883997, 360582171030029113, 360582170885581979, 360582170700566439, 360582170515219399, 360582170485842795, 360582170300707154, 360582170037742821]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579133465154650, 360579175248558287⟩, ⟨237500637394825062, 239760743022628690⟩, true⟩

def words08 : List Nat := [360582169774491108, 360582169629243739, 360582169604408607, 360582169646701445, 360582169647760122, 360582169564392831, 360582169408146720, 360582169187122536, 360582168965767150, 360582168889999449]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571570782853551, 360571612577173063⟩, ⟨843193629587168216, 845454609520948944⟩, true⟩

def words09 : List Nat := [360582168853658609, 360582168697328532, 360582168540787741, 360582168377564303, 360582168334398359, 360582168234597330, 360582168134674066, 360582167956908478, 360582167696509613, 360582167566055972]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk800

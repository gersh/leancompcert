import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk568

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575003840401946, 360575024290473083⟩, ⟨385028200489068375, 385812979498927533⟩, true⟩

def state01 : KState := ⟨⟨360623722230383072, 360623742687922599⟩, ⟨(-2382482294126705875), (-2381697090875581987)⟩, true⟩

def words00 : List Nat := [360581816763767428, 360581817029280568, 360581817492741650, 360581817956343083, 360581818120682449, 360581818121473849, 360581818141383347, 360581818306671887, 360581818781254818, 360581819520034768]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360602936431984709, 360602956897065487⟩, ⟨(-1201455949069821084), (-1200670317362465608)⟩, true⟩

def words01 : List Nat := [360581820070524603, 360581820621094635, 360581821480996416, 360581822565119513, 360581823448516300, 360581824332007078, 360581825021398920, 360581825402219644, 360581825774773103, 360581826147565083]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615398368174385, 360615418840711299⟩, ⟨(-1909644621858584916), (-1908858566456996736)⟩, true⟩

def words02 : List Nat := [360581826829520232, 360581827202998135, 360581827363080029, 360581827523238691, 360581827603242372, 360581827996940164, 360581828699739507, 360581829402665791, 360581829915618404, 360581830507469636]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360612395287793620, 360612415767814737⟩, ⟨(-1739055841789999621), (-1738269361023717903)⟩, true⟩

def words03 : List Nat := [360581831201617255, 360581831895971497, 360581832482286397, 360581832835108162, 360581832922174568, 360581833009295943, 360581833142869462, 360581833430953355, 360581833969636109, 360581834508494463]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600086848102285, 360600107335663480⟩, ⟨(-1039479305279389064), (-1038692395897483540)⟩, true⟩

def words04 : List Nat := [360581834891683667, 360581835056622417, 360581835530595391, 360581836004792158, 360581836400117651, 360581836600486832, 360581836601204608, 360581836563925602, 360581836580213991, 360581836902497881]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360590241475685177, 360590261970697658⟩, ⟨(-479607299852692593), (-478819966827490793)⟩, true⟩

def words05 : List Nat := [360581837470107739, 360581838037849496, 360581838451028751, 360581838955250411, 360581839335783779, 360581839716514942, 360581840406035538, 360581840787527990, 360581840936342242, 360581841085260760]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590651451093825, 360590671953599876⟩, ⟨(-502909697336205017), (-502121938191329257)⟩, true⟩

def words06 : List Nat := [360581841225858195, 360581841561079565, 360581842120368532, 360581842679789557, 360581842925924337, 360581842926716684, 360581842864661946, 360581842796388983, 360581842727871999, 360581842815054901]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360573510663917092, 360573531173965828⟩, ⟨472009878151291281, 472798066286416785⟩, true⟩

def words07 : List Nat := [360581842815767611, 360581842781267853, 360581843020202178, 360581843448691175, 360581843621330798, 360581843794078306, 360581843811399717, 360581843812192203, 360581843521482507, 360581843376256377]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580761385200586, 360580781902724732⟩, ⟨59564699132226523, 60353312505341751⟩, true⟩

def words08 : List Nat := [360581843230768265, 360581843177784654, 360581843178490864, 360581843042955188, 360581842907295514, 360581842639651553, 360581842717951686, 360581842875658308, 360581842876384564, 360581842780075855]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617528638979370, 360617549163982341⟩, ⟨(-2032311191931178791), (-2031522153050049949)⟩, true⟩

def words09 : List Nat := [360581843052089534, 360581843342978923, 360581843942276136, 360581844233874189, 360581844263758606, 360581844293717555, 360581844632140532, 360581845158000493, 360581845786130100, 360581846414416428]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk568

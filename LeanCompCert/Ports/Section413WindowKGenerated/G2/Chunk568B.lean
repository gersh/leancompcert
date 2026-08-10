import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk568A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk568B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk568A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk568B

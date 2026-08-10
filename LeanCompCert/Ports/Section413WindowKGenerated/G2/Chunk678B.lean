import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk678A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk678B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk678A

def state06 : KState := ⟨⟨360572421360956838, 360572450967369482⟩, ⟨703519578251311376, 704876687572333176⟩, true⟩

def words05 : List Nat := [360582839608448096, 360582839277327190, 360582838946032499, 360582838848146685, 360582838848949352, 360582838757581523, 360582838666111818, 360582838466012545, 360582838338422131, 360582838186461324]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575552532084409, 360575582147517780⟩, ⟨490951132138636675, 492308853652948323⟩, true⟩

def words06 : List Nat := [360582838042506697, 360582838043465513, 360582837835718099, 360582837519368861, 360582837202884186, 360582836736856989, 360582836379886149, 360582836239982261, 360582836099983505, 360582835850975169]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575149861253002, 360575179485744589⟩, ⟨518259081611620091, 519617417951714413⟩, true⟩

def words07 : List Nat := [360582835791212492, 360582835838622877, 360582835848937752, 360582835849896707, 360582835643442706, 360582835255144318, 360582834866673655, 360582834645951147, 360582834538862216, 360582834427081533]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575341579595849, 360575371213217978⟩, ⟨505095879079694548, 506454835246351492⟩, true⟩

def words08 : List Nat := [360582834315173981, 360582834008444623, 360582833484705156, 360582833178024483, 360582832871098817, 360582832509522131, 360582832239748420, 360582831836243607, 360582831432567702, 360582831145980482]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555260476140209, 360555290118812386⟩, ⟨1868557816666263826, 1869917387284762540⟩, true⟩

def words09 : List Nat := [360582831143702911, 360582831251493414, 360582831252363120, 360582831181333203, 360582830949121108, 360582830612180671, 360582830274957255, 360582830076236074, 360582829807447036, 360582829402866654]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk678B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk824A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk824B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk824A

def state06 : KState := ⟨⟨360567971704471326, 360568016097958370⟩, ⟨1180853913840205740, 1183326170002814552⟩, true⟩

def words05 : List Nat := [360582368711520909, 360582368562891556, 360582368413935412, 360582368261072928, 360582367961442448, 360582367522970019, 360582367084273741, 360582366792958355, 360582366575978443, 360582366403197308]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556736398563142, 360556780803292593⟩, ⟨2107273223335208749, 2109746406602755401⟩, true⟩

def words06 : List Nat := [360582366230224965, 360582365983648142, 360582365590190671, 360582365344075668, 360582365097653203, 360582364814564097, 360582364384738886, 360582363804026870, 360582363223102153, 360582362789549448]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566331314842132, 360566375730705278⟩, ⟨1315970241612325403, 1318444343130047767⟩, true⟩

def words07 : List Nat := [360582362480311221, 360582362318274341, 360582362156107164, 360582361900072776, 360582361689031389, 360582361439373367, 360582361189360900, 360582361044297505, 360582360941997757, 360582360749414421]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581749202996560, 360581793630033105⟩, ⟨44227768747937493, 46702791902052851⟩, true⟩

def words08 : List Nat := [360582360556584280, 360582360359993410, 360582360295075122, 360582360336784280, 360582360337891410, 360582360253685117, 360582360022643247, 360582359938886962, 360582359854769309, 360582359793106230]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592368016067625, 360592412454360730⟩, ⟨(-831809607598045529), (-829333655835576119)⟩, true⟩

def words09 : List Nat := [360582359787296990, 360582359700374056, 360582359672016157, 360582359806131250, 360582359839522135, 360582359873087955, 360582359874141416, 360582359826062558, 360582359923839428, 360582360047046449]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk824B

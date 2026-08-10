import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk231A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk231B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk231A

def state06 : KState := ⟨⟨360645184358344446, 360645187512396761⟩, ⟨(-1493918368630266434), (-1493868947574403736)⟩, true⟩

def words05 : List Nat := [360580659091261800, 360580662450521159, 360580666151329306, 360580671236000506, 360580675074722995, 360580678913166313, 360580681688370067, 360580682613172498, 360580685398601357, 360580688183888735]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360650479726755587, 360650482883644440⟩, ⟨(-1616935189874172568), (-1616885703110350710)⟩, true⟩

def words06 : List Nat := [360580690701827335, 360580692233257415, 360580692341684669, 360580692450130783, 360580692450382692, 360580692407645244, 360580695015353359, 360580697622893700, 360580699296659486, 360580702308653704]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360610433821191645, 360610436980918345⟩, ⟨(-688917702041948296), (-688868149510928688)⟩, true⟩

def words07 : List Nat := [360580704973870690, 360580707638944424, 360580712162939856, 360580714838721233, 360580715883867400, 360580716928944038, 360580716929193441, 360580717486444435, 360580718768806995, 360580720051126234]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588782698636701, 360588785861227805⟩, ⟨(-187306100732077615), (-187256481790150353)⟩, true⟩

def words08 : List Nat := [360580720401105719, 360580720401406634, 360580719986393400, 360580720397198414, 360580720397450394, 360580720330006072, 360580718416800189, 360580715319009171, 360580712221425011, 360580711328788922]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360516794980259474, 360516798145688916⟩, ⟨1482421739370864308, 1482471424148224430⟩, true⟩

def words09 : List Nat := [360580711609994932, 360580711891231334, 360580711891502237, 360580711226274360, 360580708716072479, 360580705729090702, 360580702742278741, 360580701610784715, 360580700530141112, 360580697776040133]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk231B

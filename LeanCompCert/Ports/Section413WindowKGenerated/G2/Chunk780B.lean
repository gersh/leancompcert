import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk780A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk780B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk780A

def state06 : KState := ⟨⟨360599098737069141, 360599138349732792⟩, ⟨(-1321809158320378902), (-1319720713858816944)⟩, true⟩

def words05 : List Nat := [360582230088960348, 360582230236360757, 360582230507732802, 360582230861360246, 360582231147882702, 360582231434586841, 360582231585827820, 360582231639636024, 360582231857123266, 360582232074975118]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593819284274554, 360593858907435120⟩, ⟨(-909664535712421414), (-907575271809106588)⟩, true⟩

def words06 : List Nat := [360582232425630603, 360582232699848944, 360582232891959988, 360582233084210449, 360582233185673645, 360582233369879816, 360582233530088679, 360582233690501390, 360582233758697504, 360582233908756878]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613321159908115, 360613360793608232⟩, ⟨(-2432390689887499395), (-2430300603111016941)⟩, true⟩

def words07 : List Nat := [360582234000247815, 360582234092045809, 360582234306532179, 360582234400246622, 360582234401285847, 360582234351048170, 360582234380638739, 360582234616740951, 360582235016287068, 360582235416075785]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580160700197048, 360580200344509621⟩, ⟨156868766504001709, 158959681952183535⟩, true⟩

def words08 : List Nat := [360582235700910811, 360582235822275907, 360582236078474141, 360582236335005626, 360582236440638792, 360582236441753807, 360582236383853945, 360582236244139312, 360582236104221280, 360582235940385562]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554312379542485, 360554352034371856⟩, ⟨2175520468211328010, 2177612204970007910⟩, true⟩

def words09 : List Nat := [360582235937878903, 360582235961667204, 360582235962670252, 360582235903508728, 360582235680624134, 360582235417019435, 360582235153095150, 360582234978314817, 360582234748799432, 360582234392950218]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk780B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk588A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk588B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk588A

def state06 : KState := ⟨⟨360581782972830712, 360581804995971273⟩, ⟨14311073930918268, 15186833824486192⟩, true⟩

def words05 : List Nat := [360582062139638462, 360582062093116104, 360582062226088390, 360582062612998590, 360582062878270431, 360582063143681730, 360582063223237178, 360582063224059409, 360582063015612627, 360582063012176243]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574617464567694, 360574639495461523⟩, ⟨436023196522293152, 436899412811791500⟩, true⟩

def words06 : List Nat := [360582063047022413, 360582063047846447, 360582062963335950, 360582062659121751, 360582062354779899, 360582061934700453, 360582061658315372, 360582061468298485, 360582061278205574, 360582060922551923]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575778722128843, 360575800760782364⟩, ⟨367626052894764226, 368502726036214720⟩, true⟩

def words07 : List Nat := [360582060797155981, 360582060767501287, 360582060938243453, 360582060939065887, 360582060852700663, 360582060512997222, 360582060173162179, 360582059715328415, 360582059404370739, 360582059298928360]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360553254871431309, 360553276917917076⟩, ⟨1693755763486393437, 1694632897829314581⟩, true⟩

def words08 : List Nat := [360582059193371251, 360582058914327550, 360582058446968271, 360582057930955362, 360582057414726329, 360582056824527042, 360582055946621657, 360582054921628667, 360582053896510653, 360582053160026591]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360540262928510503, 360540284982751693⟩, ⟨2458881633899792371, 2459759224998259815⟩, true⟩

def words09 : List Nat := [360582052672067773, 360582052118191307, 360582051564243866, 360582050839958671, 360582050073803331, 360582049233831419, 360582048393638220, 360582047841906237, 360582047307657570, 360582046599474924]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk588B

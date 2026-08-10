import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk871A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk871B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk871A

def state06 : KState := ⟨⟨362474218612284976, 362474333282773873⟩, ⟨939901027502692375, 946649454515366081⟩, true⟩

def words05 : List Nat := [371285194166461036, 371285194340054093, 371285194489280839, 371285194492314408, 371285194477779579, 371285194493237101, 371285194561619097, 371285194564652738, 371285194457810364, 371285194336634766]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487216976264192, 362487331673911741⟩, ⟨(-193076741482210170), (-186325947185560090)⟩, true⟩

def words06 : List Nat := [371285194214083735, 371285194201488582, 371285194169014773, 371285194211665581, 371285194236140681, 371285194239176001, 371285194110368721, 371285194095185412, 371285194169937911, 371285194197604420]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496163608719508, 362496278334018216⟩, ⟨(-973021063729881098), (-966267858941382932)⟩, true⟩

def words07 : List Nat := [371285194199912620, 371285194198309255, 371285194312371721, 371285194382253499, 371285194456609916, 371285194532146445, 371285194606746700, 371285194609848916, 371285194734755466, 371285194865614076]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492564913819951, 362492679666107156⟩, ⟨(-659253803467236043), (-652498245678668585)⟩, true⟩

def words08 : List Nat := [371285195126222282, 371285195212500647, 371285195296826583, 371285195382192319, 371285195468487349, 371285195510087620, 371285195681777438, 371285195854672064, 371285196026703173, 371285196115675591]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489432509629720, 362489547289434898⟩, ⟨(-386126704523099549), (-379368747306219983)⟩, true⟩

def words09 : List Nat := [371285196262259926, 371285196410526602, 371285196602641800, 371285196620465761, 371285196622814328, 371285196619543501, 371285196676210699, 371285196679555633, 371285196726947384, 371285196780297317]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk871B

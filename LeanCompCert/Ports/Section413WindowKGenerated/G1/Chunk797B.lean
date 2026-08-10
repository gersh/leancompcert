import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk797A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk797B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk797A

def state06 : KState := ⟨⟨362482446325285238, 362482541697367446⟩, ⟨206234770070177793, 211371410871607967⟩, true⟩

def words05 : List Nat := [371285193294505198, 371285193107943946, 371285192919933317, 371285192878213211, 371285192626416708, 371285192360700958, 371285192093894601, 371285191985436917, 371285191820373980, 371285191790282086]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469466411445589, 362469561808371819⟩, ⟨1241529286026335677, 1246667908513740323⟩, true⟩

def words06 : List Nat := [371285191759131096, 371285191699498925, 371285191476079032, 371285191376621036, 371285191275853394, 371285191174769592, 371285190863611851, 371285190553246970, 371285190241728007, 371285190088533707]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362461913959712089, 362462009381474017⟩, ⟨1844086226647577587, 1849226830403013625⟩, true⟩

def words07 : List Nat := [371285189894489102, 371285189843606939, 371285189791745308, 371285189740484707, 371285189479050629, 371285189265822470, 371285189051098116, 371285188994269289, 371285188746787556, 371285188459318126]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468391137654410, 362468486584074456⟩, ⟨1327291954349909871, 1332434525456667985⟩, true⟩

def words08 : List Nat := [371285188170672436, 371285187927756464, 371285187605195313, 371285187364482260, 371285187122914428, 371285186863647406, 371285186490648525, 371285186230533720, 371285185969024928, 371285185851218919]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472619074467723, 362472714546102054⟩, ⟨989922532953910678, 995067116025919046⟩, true⟩

def words09 : List Nat := [371285185643992619, 371285185437665646, 371285185230217739, 371285185089002002, 371285184912411683, 371285184785072064, 371285184656829625, 371285184515045149, 371285184211582035, 371285184058834209]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk797B

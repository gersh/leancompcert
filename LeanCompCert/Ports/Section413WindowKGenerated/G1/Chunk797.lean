import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk797

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489660934525784, 362489756157612863⟩, ⟨(-368303114767327732), (-363178353356472012)⟩, true⟩

def state01 : KState := ⟨⟨362479463371610672, 362479558619573199⟩, ⟨444490218093022353, 449616962202718385⟩, true⟩

def words00 : List Nat := [371285199458381163, 371285199461183475, 371285199423883196, 371285199459722241, 371285199529717648, 371285199532490820, 371285199461434185, 371285199384712013, 371285199306928545, 371285199278991123]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467944352524777, 362468039625320217⟩, ⟨1362779279524375812, 1367908003189833650⟩, true⟩

def words01 : List Nat := [371285199279668953, 371285199352270873, 371285199403766581, 371285199406521321, 371285199248176720, 371285199124764528, 371285198999896266, 371285198956751150, 371285198743653392, 371285198531531831]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473732929472430, 362473828226981775⟩, ⟨901295767492533274, 906426461473038708⟩, true⟩

def words02 : List Nat := [371285198318164958, 371285198224228021, 371285198059968806, 371285197963262614, 371285197865721849, 371285197744760050, 371285197413293689, 371285197217159723, 371285197019550439, 371285196927113132]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468379353046133, 362468474675610369⟩, ⟨1328206783382404645, 1333339475118841327⟩, true⟩

def words03 : List Nat := [371285196786605965, 371285196647663238, 371285196507625097, 371285196507802674, 371285196432453846, 371285196384700827, 371285196336029466, 371285196257660360, 371285195968864732, 371285195762582013]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362464771428102508, 362464866775228089⟩, ⟨1615925436810379346, 1621060087193366966⟩, true⟩

def words04 : List Nat := [371285195554761218, 371285195459345548, 371285195212756295, 371285194960513044, 371285194707128147, 371285194478839907, 371285194170834410, 371285193963432082, 371285193755148389, 371285193547481298]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk797

import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk982A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk982B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk982A

def state06 : KState := ⟨⟨362472615139999372, 362472762231603156⟩, ⟨1227845789436051369, 1237603843879679951⟩, true⟩

def words05 : List Nat := [371285357951868363, 371285357941698830, 371285357930327393, 371285357919184229, 371285357807907249, 371285357723676454, 371285357652824435, 371285357656275646, 371285357550760213, 371285357426431975]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483215781846115, 362483362904311864⟩, ⟨186183325200296860, 195944412299237696⟩, true⟩

def words06 : List Nat := [371285357300590706, 371285357262565013, 371285357177560720, 371285357146951049, 371285357115235378, 371285357068378821, 371285356934265064, 371285356870263620, 371285356840008510, 371285356843584269]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476732662846225, 362476879816897967⟩, ⟨823324708255785877, 833088899453134955⟩, true⟩

def words07 : List Nat := [371285356825898025, 371285356802756616, 371285356783241243, 371285356787070908, 371285356757952249, 371285356761931962, 371285356764520318, 371285356745181270, 371285356586727617, 371285356504926591]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462222458134541, 362462369642874811⟩, ⟨2249486027842679775, 2259253235273020629⟩, true⟩

def words08 : List Nat := [371285356421019305, 371285356414785816, 371285356279120936, 371285356145032135, 371285356009670770, 371285355881022258, 371285355699302164, 371285355546829274, 371285355393172233, 371285355228745938]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486194815926858, 362486342031824914⟩, ⟨(-106884529257421771), (-97114259169947125)⟩, true⟩

def words09 : List Nat := [371285354997233939, 371285354859453148, 371285354719932579, 371285354649936763, 371285354515911974, 371285354367080478, 371285354216789442, 371285354171551326, 371285354090444412, 371285354104345337]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk982B

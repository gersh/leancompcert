import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk246A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk246B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk246A

def state06 : KState := ⟨⟨360613618103828856, 360613621699713267⟩, ⟨(-741270803097967106), (-741210814100185594)⟩, true⟩

def words05 : List Nat := [360583554810443550, 360583554791823914, 360583555933394720, 360583558400881418, 360583560441891052, 360583562482787957, 360583563692351142, 360583563692672923, 360583564488714872, 360583565707900276]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 24650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 24600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604452252109384, 360604455851028599⟩, ⟨(-515274204208876341), (-515214140357336453)⟩, true⟩

def words06 : List Nat := [360583566210506274, 360583567374593932, 360583567708039928, 360583568041493951, 360583568041763511, 360583568677166594, 360583569928483117, 360583571179764392, 360583571613145568, 360583572459988215]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 24660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 24600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360660783075824437, 360660786677782270⟩, ⟨(-1905182564714907603), (-1905122425885775179)⟩, true⟩

def words07 : List Nat := [360583574947010320, 360583577433924725, 360583580154896021, 360583582641101762, 360583583597786838, 360583584554414269, 360583587150436772, 360583590582293858, 360583593710435880, 360583596838396274]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 24670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 24600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360651773192514197, 360651776797543325⟩, ⟨(-1682812193944043222), (-1682751979300380116)⟩, true⟩

def words08 : List Nat := [360583598961045783, 360583601844910517, 360583606367559233, 360583610889938710, 360583614987347342, 360583617455570980, 360583618853214000, 360583620250774939, 360583621593478504, 360583624354171231]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 24680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 24600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360599759339381343, 360599762947445083⟩, ⟨(-398172781164560138), (-398112491581042686)⟩, true⟩

def words09 : List Nat := [360583628752462932, 360583633150459846, 360583636719520916, 360583638660046336, 360583639527209399, 360583640394394817, 360583642898674098, 360583644379609335, 360583645032470120, 360583645685326908]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 24690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 24600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 24600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk246B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk306A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk306B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk306A

def state06 : KState := ⟨⟨360527100591699936, 360527106256211739⟩, ⟨1724833395084891489, 1724950845061143127⟩, true⟩

def words05 : List Nat := [360583370755462702, 360583370839122591, 360583370839457894, 360583370917863933, 360583371043094920, 360583371168384087, 360583371168749309, 360583370473763101, 360583368718477029, 360583366883904536]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360500117455732331, 360500123124077484⟩, ⟨2552302244404296322, 2552419811930782806⟩, true⟩

def words06 : List Nat := [360583365049309289, 360583364274287132, 360583362439144085, 360583360062516688, 360583357685977999, 360583355041343223, 360583353059019581, 360583350602024615, 360583348145141598, 360583345159027950]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579148399687159, 360579154071876671⟩, ⟨128062422351810980, 128180107804094966⟩, true⟩

def words07 : List Nat := [360583342445978954, 360583340791931202, 360583339137867888, 360583338082153875, 360583337094588566, 360583335202259868, 360583333309976762, 360583332476224606, 360583332177251931, 360583332041492190]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573213292380672, 360573218968459542⟩, ⟨309894744652316094, 310012549448356670⟩, true⟩

def words08 : List Nat := [360583331905690382, 360583330962642490, 360583329912598033, 360583329592927951, 360583329273172741, 360583328189745283, 360583326436341180, 360583324067422485, 360583321698573394, 360583320387470567]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360513174883344008, 360513180563255707⟩, ⟨2152898923303750002, 2153016845749151244⟩, true⟩

def words09 : List Nat := [360583320441634245, 360583320824983632, 360583320825348531, 360583320529923535, 360583319540786508, 360583317813642754, 360583316086492436, 360583315416531003, 360583313689181155, 360583311405136787]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk306B

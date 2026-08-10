import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk459A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk459B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk459A

def state06 : KState := ⟨⟨360594766511358530, 360594779671455056⟩, ⟨(-531296960543686724), (-530888236185669682)⟩, true⟩

def words05 : List Nat := [360583228497836082, 360583228181496728, 360583228020614503, 360583228529091803, 360583228613710636, 360583228698416894, 360583228698978323, 360583228546899416, 360583228577695147, 360583228829737390]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588879368148114, 360588892534189315⟩, ⟨(-260703839314299735), (-260294841709511975)⟩, true⟩

def words06 : List Nat := [360583229034044544, 360583229327021366, 360583229381594854, 360583229436229555, 360583229436757579, 360583229398396115, 360583229826403962, 360583230254518305, 360583230257232499, 360583230381055611]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360634281338068017, 360634294510057739⟩, ⟨(-2348111282793962691), (-2347702011706650761)⟩, true⟩

def words07 : List Nat := [360583230976881367, 360583231572872278, 360583232449336141, 360583232977797137, 360583233099547402, 360583233221351761, 360583233559248557, 360583234198493261, 360583235309492727, 360583236420592381]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599642760027712, 360599655938032125⟩, ⟨(-755508138602009462), (-755098590929791440)⟩, true⟩

def words08 : List Nat := [360583237216297443, 360583237667141054, 360583238106054048, 360583238545123850, 360583238697156059, 360583238697786704, 360583238378145365, 360583237822147965, 360583237266054089, 360583237538977315]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552277698776735, 360552290882717484⟩, ⟨1423116039313492172, 1423525860027907712⟩, true⟩

def words09 : List Nat := [360583237798244449, 360583238057617320, 360583238080565573, 360583238189802676, 360583238190330633, 360583238179864325, 360583238169222592, 360583238147039088, 360583237769169756, 360583237097065917]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk459B

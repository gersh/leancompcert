import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk627A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571599998459027, 360571625114551805⟩, ⟨691549407547534276, 692613224590044056⟩, true⟩

def state01 : KState := ⟨⟨360583324558549790, 360583349682917796⟩, ⟨(-43652668130764630), (-42588332188477706)⟩, true⟩

def words00 : List Nat := [360582671480008414, 360582671480888783, 360582671363006883, 360582671118643487, 360582670874144267, 360582670565407035, 360582670527782125, 360582670603215231, 360582670603999486, 360582670562313939]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572120489910953, 360572145622602498⟩, ⟨658913568042336013, 659978425995068499⟩, true⟩

def words01 : List Nat := [360582670612726993, 360582670663405732, 360582670664132430, 360582670575613484, 360582670233561959, 360582669659029276, 360582669084346417, 360582668681185337, 360582668404659315, 360582668237812879]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568852779424701, 360568877920509066⟩, ⟨863769549846017691, 864834934236066387⟩, true⟩

def words02 : List Nat := [360582668070837904, 360582667729985706, 360582667349559698, 360582667223366030, 360582667096947456, 360582666826063817, 360582666373147393, 360582665698508748, 360582665023722965, 360582664544679895]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574379236875017, 360574404386248813⟩, ⟨517108894010014945, 518174798439017927⟩, true⟩

def words03 : List Nat := [360582664359743601, 360582664394748622, 360582664395538514, 360582664238225431, 360582664087599254, 360582663872901771, 360582663657953056, 360582663603394024, 360582663598879523, 360582663468149340]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594889553437977, 360594914711138790⟩, ⟨(-769831075389401889), (-768764648483266097)⟩, true⟩

def words04 : List Nat := [360582663337236180, 360582663199874104, 360582663431193485, 360582663674271756, 360582663692623954, 360582663693504999, 360582663525606099, 360582663443875821, 360582663480767863, 360582663676916495]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk627A

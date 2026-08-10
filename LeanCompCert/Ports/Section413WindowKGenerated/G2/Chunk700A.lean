import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk700A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360535467402754303, 360535498983749457⟩, ⟨3292658543057464593, 3294151772067183613⟩, true⟩

def state01 : KState := ⟨⟨360575503723251035, 360575535313601009⟩, ⟨489951699504369525, 491445583398070135⟩, true⟩

def words00 : List Nat := [360582557623314246, 360582557155701381, 360582556789789839, 360582556627611993, 360582556465358623, 360582556125995063, 360582555820165455, 360582555466381580, 360582555112316957, 360582554961985498]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 70000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 70000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580337577180962, 360580369176982659⟩, ⟨151480231593295256, 152974777248512400⟩, true⟩

def words01 : List Nat := [360582554862613142, 360582554659649382, 360582554456500400, 360582554489824446, 360582554490661923, 360582554417930647, 360582554345093416, 360582554170633836, 360582553936795175, 360582553906734852]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 70010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 70000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576424121233950, 360576455730383836⟩, ⟨425431567872396179, 426926768134034367⟩, true⟩

def words02 : List Nat := [360582553876349844, 360582553836055105, 360582553647878713, 360582553316099192, 360582552984168445, 360582552601182267, 360582552371532114, 360582552310990412, 360582552250333470, 360582552071496703]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 70020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 70000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595715336686022, 360595746955199731⟩, ⟨(-925680209002456557), (-924184352946600411)⟩, true⟩

def words03 : List Nat := [360582551985250413, 360582551959169575, 360582552043113576, 360582552101710526, 360582552102643502, 360582551953118417, 360582551803413127, 360582551686321759, 360582551860609913, 360582552050030665]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 70030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 70000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582911530429257, 360582943158401219⟩, ⟨(-28879416872137634), (-27382898312990216)⟩, true⟩

def words04 : List Nat := [360582552106866399, 360582552169581990, 360582552386265959, 360582552603239947, 360582552768854052, 360582552769846240, 360582552731984492, 360582552573861519, 360582552415560444, 360582552258937786]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 70040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 70000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk700A

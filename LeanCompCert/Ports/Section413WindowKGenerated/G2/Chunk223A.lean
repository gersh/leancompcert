import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk223A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581987610056113, 360581990524470147⟩, ⟨(-41575804437695370), (-41531831063728534)⟩, true⟩

def state01 : KState := ⟨⟨360702371196511084, 360702374113654351⟩, ⟨(-2726643758848989678), (-2726599724600217166)⟩, true⟩

def words00 : List Nat := [360580129323631601, 360580132111268625, 360580136904842064, 360580141698041612, 360580144778092102, 360580147064579823, 360580151356659335, 360580155648441720, 360580159872001681, 360580165350057910]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360644834292232091, 360644837212123607⟩, ⟨(-1442595468171054986), (-1442551372594999376)⟩, true⟩

def words01 : List Nat := [360580169367243604, 360580173384098242, 360580178701877257, 360580185030092329, 360580190843975156, 360580196657388899, 360580201266430758, 360580203877957442, 360580206773951319, 360580209669782539]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360607564101537487, 360607567024153397⟩, ⟨(-611012886992000462), (-610968730594009114)⟩, true⟩

def words02 : List Nat := [360580211984951054, 360580212303187995, 360580212303449690, 360580211088985580, 360580209874584119, 360580207546130880, 360580206644199575, 360580206905367108, 360580206905627069, 360580207356848126]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360670287321772801, 360670290247113210⟩, ⟨(-2012001172108903006), (-2011956954859008028)⟩, true⟩

def words03 : List Nat := [360580209980724452, 360580212604450036, 360580216125117278, 360580219099939459, 360580220367943247, 360580221635856226, 360580222836874406, 360580225473991527, 360580229505773034, 360580233537258727]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360625760936682115, 360625763864774833⟩, ⟨(-1017510662322042787), (-1017466383572064631)⟩, true⟩

def words04 : List Nat := [360580236072764451, 360580236615074492, 360580239155988053, 360580241696764612, 360580243265199082, 360580243265488265, 360580242841157676, 360580241108567858, 360580239641466574, 360580241678583072]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk223A

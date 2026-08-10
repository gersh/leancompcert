import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk293A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360611339110897218, 360611344263775904⟩, ⟨(-823535443011369180), (-823433334618160730)⟩, true⟩

def state01 : KState := ⟨⟨360609182162173436, 360609187318748684⟩, ⟨(-760303442375088173), (-760201225654615607)⟩, true⟩

def words00 : List Nat := [360583242073810257, 360583243161613320, 360583245410890332, 360583247660134085, 360583249615718755, 360583250413715701, 360583250630351737, 360583250847016332, 360583250847335463, 360583251621377233]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360529143656485925, 360529148816711431⟩, ⟨1586221246112407417, 1586323569840544433⟩, true⟩

def words01 : List Nat := [360583253667524282, 360583255713605841, 360583257167462449, 360583257464115279, 360583257464443676, 360583256667698009, 360583255870886765, 360583255569924576, 360583254466906624, 360583252621958380]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360619363311783109, 360619368475677495⟩, ⟨(-1059640576885566869), (-1059538145568268425)⟩, true⟩

def words02 : List Nat := [360583250777048498, 360583249813826562, 360583249443148861, 360583248676290054, 360583247909455074, 360583245934322416, 360583244298980182, 360583243823612300, 360583243751587971, 360583244983618982]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360612910259413768, 360612915427002962⟩, ⟨(-870294879079554605), (-870192339374801093)⟩, true⟩

def words03 : List Nat := [360583245625071601, 360583246266519684, 360583248067123788, 360583250455762986, 360583252551726519, 360583254647611260, 360583255655549986, 360583255655938221, 360583256519284148, 360583257530565390]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360618518037424661, 360618523208670469⟩, ⟨(-1035014520879511861), (-1034911873871428491)⟩, true⟩

def words04 : List Nat := [360583258347002328, 360583258792528430, 360583258792874377, 360583258658251291, 360583258523567488, 360583258389307073, 360583259839922444, 360583261290516620, 360583262156347526, 360583263358107578]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk293A

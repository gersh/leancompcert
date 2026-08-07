import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk293

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

def state06 : KState := ⟨⟨360637638700321958, 360637643875239929⟩, ⟨(-1596339681595709351), (-1596236926791644927)⟩, true⟩

def words05 : List Nat := [360583264485225399, 360583265612374436, 360583267608644480, 360583269267990800, 360583269950235470, 360583270632463520, 360583271995183299, 360583274279957088, 360583276132099766, 360583277984201081]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608183432212697, 360608188610827553⟩, ⟨(-731628027624772729), (-731525164261628413)⟩, true⟩

def words06 : List Nat := [360583279257184968, 360583279784614757, 360583281468717592, 360583283152819272, 360583284027168696, 360583284027557363, 360583283748858573, 360583282718170416, 360583281687478365, 360583282235005769]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552437497909265, 360552442680190245⟩, ⟨906047873346195656, 906150844401836092⟩, true⟩

def words07 : List Nat := [360583283606105396, 360583284977192173, 360583285770087115, 360583286077883782, 360583286078209697, 360583285952328831, 360583286307339147, 360583286307728169, 360583286168141713, 360583285118733535]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360661221371804886, 360661226557752159⟩, ⟨(-2290663105865164655), (-2290560027075192711)⟩, true⟩

def words08 : List Nat := [360583284069309255, 360583283187204458, 360583284009489920, 360583284998321200, 360583285015348327, 360583285067641002, 360583286274650653, 360583287481692219, 360583289843260744, 360583292495383571]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360604642516659828, 360604647706318786⟩, ⟨(-627639095371235363), (-627535907477049737)⟩, true⟩

def words09 : List Nat := [360583294380451538, 360583296265436261, 360583297215655537, 360583298979543303, 360583300452721345, 360583301925862597, 360583302648369512, 360583302648758693, 360583302947109522, 360583303673548573]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk293

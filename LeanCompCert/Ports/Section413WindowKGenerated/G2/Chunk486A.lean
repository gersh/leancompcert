import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk486A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572665794269996, 360572680577510355⟩, ⟨458808808668464591, 459294296695742179⟩, true⟩

def state01 : KState := ⟨⟨360545352277634083, 360545367067183793⟩, ⟨1786317431985737298, 1786803226679531676⟩, true⟩

def words00 : List Nat := [360582130883542093, 360582130578520903, 360582130095843400, 360582129312653430, 360582128529385888, 360582127640834023, 360582126965920375, 360582126417083330, 360582125868193026, 360582125002314004]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596997063503042, 360597011859369001⟩, ⟨(-724445393473664140), (-723959291716586700)⟩, true⟩

def words01 : List Nat := [360582124246690113, 360582123913099146, 360582123587246689, 360582123587916086, 360582123290442499, 360582122600339993, 360582121910137585, 360582121513158965, 360582121704579190, 360582122011531306]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602085756255322, 360602100558496659⟩, ⟨(-971922797425715944), (-971436385665912366)⟩, true⟩

def words02 : List Nat := [360582122056041558, 360582122259407697, 360582122884225478, 360582123509213874, 360582124019084938, 360582124296662432, 360582124362878793, 360582124429159568, 360582124485644733, 360582124897176392]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360540613381433963, 360540628189982216⟩, ⟨2017826074627927870, 2018312793124816730⟩, true⟩

def words03 : List Nat := [360582125373157338, 360582125849243408, 360582126016256490, 360582126016926220, 360582125761283492, 360582125316905834, 360582124872331929, 360582124572899483, 360582123960029562, 360582123107604026]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603362004357553, 360603376819235901⟩, ⟨(-1034658818410614771), (-1034171791987441281)⟩, true⟩

def words04 : List Nat := [360582122255060380, 360582121728044184, 360582121549828842, 360582121362222940, 360582121174579243, 360582120585501475, 360582119876370395, 360582119588602571, 360582119433288511, 360582119870930883]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk486A

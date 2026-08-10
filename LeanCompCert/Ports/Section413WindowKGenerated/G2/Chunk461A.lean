import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk461A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583388570264129, 360583401813951430⟩, ⟨(-9362065961099651), (-8949493920872469)⟩, true⟩

def state01 : KState := ⟨⟨360574735175131864, 360574748424844411⟩, ⟨389556585571758562, 389969435405040738⟩, true⟩

def words00 : List Nat := [360583207686540355, 360583207328491286, 360583207417349178, 360583207696899431, 360583207857439852, 360583207858072225, 360583207549102485, 360583206972094232, 360583206394998967, 360583205797115178]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360518659636693469, 360518672892361919⟩, ⟨2975531474191060541, 2975944598680918835⟩, true⟩

def words01 : List Nat := [360583205614215584, 360583205569302935, 360583205524320117, 360583205187514331, 360583204381224361, 360583203324439860, 360583202267496594, 360583201573256321, 360583200409621302, 360583199011153787]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360532314154429436, 360532327416076170⟩, ⟨2345601142503231620, 2346014542741064856⟩, true⟩

def words02 : List Nat := [360583197612605060, 360583196373022587, 360583195369340125, 360583194111483385, 360583192853635169, 360583191164423214, 360583189005960240, 360583187216794815, 360583185427521127, 360583184007074243]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360541135312374282, 360541148580046637⟩, ⟨1938676724646942461, 1939090402875735605⟩, true⟩

def words03 : List Nat := [360583182905199329, 360583181568684273, 360583180232104694, 360583179364463589, 360583178859762575, 360583178236582234, 360583177613372082, 360583176609335293, 360583175723452194, 360583174813312258]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360551118713473149, 360551131987101311⟩, ⟨1477914147709807493, 1478328100769801961⟩, true⟩

def words04 : List Nat := [360583173903002051, 360583173461396097, 360583172550761430, 360583171405630152, 360583170260437908, 360583168805372130, 360583167585862564, 360583166834984786, 360583166084070321, 360583165098710625]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk461A

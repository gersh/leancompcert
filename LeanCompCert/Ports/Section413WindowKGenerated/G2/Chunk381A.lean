import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk381A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590216347672572, 360590225253726955⟩, ⟨(-318267093275427212), (-318037731452388898)⟩, true⟩

def state01 : KState := ⟨⟨360575431248516323, 360575440159418871⟩, ⟨244933640338396290, 245163186900996806⟩, true⟩

def words00 : List Nat := [360581878226194146, 360581878226708463, 360581877742406025, 360581876816809125, 360581875891173472, 360581874791871749, 360581874130476541, 360581873935369884, 360581873740208386, 360581873200271692]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360650269908518193, 360650278824275130⟩, ⟨(-2607612396774031075), (-2607382665187173023)⟩, true⟩

def words01 : List Nat := [360581873184343102, 360581873337353990, 360581874177047084, 360581875202002961, 360581875511099958, 360581875820207624, 360581876585207463, 360581877693570153, 360581879488349503, 360581881283151152]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360635606545478394, 360635615466140732⟩, ⟨(-2048633221407701076), (-2048403302803436188)⟩, true⟩

def words02 : List Nat := [360581882640181025, 360581884037623729, 360581885903277896, 360581887768990520, 360581889381950489, 360581890891016379, 360581891994614196, 360581893098210419, 360581893899783673, 360581895309239433]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567216033242794, 360567224958749459⟩, ⟨559550124132040112, 559780227475360826⟩, true⟩

def words03 : List Nat := [360581896945750467, 360581898582273156, 360581899764681638, 360581900638825766, 360581901181738612, 360581901724768557, 360581902368102634, 360581902368617490, 360581902328558683, 360581901944262710]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360611472372959735, 360611481303334058⟩, ⟨(-1128690083618617226), (-1128459794599708046)⟩, true⟩

def words04 : List Nat := [360581901607216705, 360581902117539566, 360581902608774881, 360581903100075884, 360581903100550453, 360581903005164827, 360581902226501783, 360581901840657210, 360581901753784774, 360581902529655788]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk381A

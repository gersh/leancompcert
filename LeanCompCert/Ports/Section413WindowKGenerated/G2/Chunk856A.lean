import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk856A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360534723033280227, 360534771010903480⟩, ⟨4070630504706987084, 4073403973243799156⟩, true⟩

def state01 : KState := ⟨⟨360567079424148885, 360567127413401871⟩, ⟨1300743961031153396, 1303518425130620812⟩, true⟩

def words00 : List Nat := [360582356951001926, 360582356532834947, 360582356217701833, 360582355899219582, 360582355580654567, 360582355145132512, 360582354646998916, 360582354285600681, 360582353923835181, 360582353653620662]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567547838137360, 360567595839104090⟩, ⟨1260587510003115950, 1263362976973348334⟩, true⟩

def words01 : List Nat := [360582353476863014, 360582353231755895, 360582352986422471, 360582352722370385, 360582352540477250, 360582352324444991, 360582352108314230, 360582351783441206, 360582351475782577, 360582351304847764]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575387139938219, 360575435152488893⟩, ⟨589352826038050153, 592129284883085621⟩, true⟩

def words02 : List Nat := [360582351133507758, 360582351098712877, 360582350983311359, 360582350799609445, 360582350615682291, 360582350386717423, 360582350247486841, 360582350244781392, 360582350241946431, 360582350127204333]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583499245098864, 360583547269280693⟩, ⟨(-105431547648293709), (-102654092769100673)⟩, true⟩

def words03 : List Nat := [360582350047468182, 360582349911657115, 360582349775489823, 360582349699599868, 360582349532893016, 360582349232205458, 360582348931289722, 360582348705336526, 360582348598076878, 360582348613347565]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585098419032706, 360585146454934541⟩, ⟨(-242500019747276830), (-239721561110234568)⟩, true⟩

def words04 : List Nat := [360582348614444096, 360582348561242941, 360582348371423808, 360582348318224873, 360582348264697854, 360582348118806964, 360582348021124087, 360582347855165126, 360582347688974082, 360582347636927627]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk856A

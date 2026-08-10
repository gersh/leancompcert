import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk496A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360546741042214861, 360546756465598077⟩, ⟨1741567278098383343, 1742084198279494015⟩, true⟩

def state01 : KState := ⟨⟨360599631565388036, 360599646995239583⟩, ⟨(-881993981520511375), (-881476740478665841)⟩, true⟩

def words00 : List Nat := [360581878423335068, 360581878039068978, 360581878301690672, 360581878635986292, 360581878636616994, 360581878620742279, 360581878652960450, 360581878832632265, 360581878868332435, 360581879227194620]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583922032532066, 360583937468888093⟩, ⟨(-102502741826492600), (-101985178064382574)⟩, true⟩

def words01 : List Nat := [360581879325131818, 360581879423139126, 360581879926062236, 360581880634059200, 360581881241413874, 360581881848867535, 360581882178087793, 360581882178772114, 360581882144084013, 360581882186284672]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573394167811596, 360573409610623275⟩, ⟨419769829217977575, 420287713341723417⟩, true⟩

def words02 : List Nat := [360581882186844311, 360581882085005079, 360581881737635294, 360581881030182607, 360581880322647488, 360581879502991187, 360581878892248524, 360581878686491927, 360581878480667522, 360581878031202395]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360622018938125457, 360622034387395856⟩, ⟨(-1993737102384391361), (-1993218897682082237)⟩, true⟩

def words03 : List Nat := [360581877935409678, 360581878010447114, 360581878490019245, 360581879050683707, 360581879269809423, 360581879488973927, 360581879689171983, 360581880094190324, 360581880903653812, 360581881713241789]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593635667483156, 360593651123272417⟩, ⟨(-584849724726407151), (-584331196395819019)⟩, true⟩

def words04 : List Nat := [360581882320214693, 360581882522345342, 360581882786450694, 360581883050762521, 360581883214614595, 360581883215299350, 360581883090173211, 360581882661124613, 360581882231961574, 360581882353330305]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk496A

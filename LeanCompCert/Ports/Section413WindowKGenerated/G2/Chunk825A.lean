import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk825A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592368016067625, 360592412454360730⟩, ⟨(-831809607598045529), (-829333655835576119)⟩, true⟩

def state01 : KState := ⟨⟨360596411399951752, 360596455849383271⟩, ⟨(-1165445733115808722), (-1162968862378056546)⟩, true⟩

def words00 : List Nat := [360582360151377765, 360582360294646528, 360582360351031603, 360582360407534344, 360582360408524779, 360582360455000255, 360582360662146129, 360582360869513694, 360582360964357848, 360582361136407086]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598794316932491, 360598838777527626⟩, ⟨(-1362148054559626866), (-1359670262656949434)⟩, true⟩

def words01 : List Nat := [360582361259660884, 360582361383261491, 360582361625864792, 360582361722151695, 360582361723242463, 360582361694460995, 360582361665435087, 360582361718394549, 360582361919024200, 360582362119917358]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594708333449344, 360594752805337551⟩, ⟨(-1025061764957380539), (-1022583041097555453)⟩, true⟩

def words02 : List Nat := [360582362235604584, 360582362362076511, 360582362484195878, 360582362606651164, 360582362690009707, 360582362691192609, 360582362628105225, 360582362491480142, 360582362363613724, 360582362515130265]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559053804140169, 360559098287163777⟩, ⟨1917774909004192388, 1920254551925200552⟩, true⟩

def words03 : List Nat := [360582362812993435, 360582363111076535, 360582363275155992, 360582363363101535, 360582363364192420, 360582363365597251, 360582363366574946, 360582363306966556, 360582363100777134, 360582362820140821]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582809054030770, 360582853548221555⟩, ⟨(-43107906947958707), (-40627342233563955)⟩, true⟩

def words04 : List Nat := [360582362539243140, 360582362356002322, 360582362256402091, 360582362268146125, 360582362269237346, 360582362156009666, 360582361930854158, 360582361703092666, 360582361474976963, 360582361399825612]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk825A

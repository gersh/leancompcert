import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk713A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576364732957826, 360576397545792963⟩, ⟨419927235424752850, 421507496469494620⟩, true⟩

def state01 : KState := ⟨⟨360570431977003320, 360570464799477413⟩, ⟨842959328735193845, 844540277085966015⟩, true⟩

def words00 : List Nat := [360582309209874951, 360582309029813070, 360582309031937059, 360582309113939177, 360582309114789592, 360582309090206762, 360582308925823270, 360582308640669703, 360582308355345089, 360582308023107844]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360551730013960212, 360551762845957877⟩, ⟨2176696549893455629, 2178278177417932601⟩, true⟩

def words01 : List Nat := [360582307857847757, 360582307800372749, 360582307742795340, 360582307535635881, 360582307170686900, 360582306688918955, 360582306206837949, 360582305921183852, 360582305591968804, 360582305164766317]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584225585292151, 360584258426845830⟩, ⟨(-141123564834741563), (-139541255727571697)⟩, true⟩

def words02 : List Nat := [360582304737346854, 360582304456071721, 360582304273557058, 360582304026266433, 360582303778907308, 360582303364129348, 360582302864185697, 360582302560713265, 360582302256952709, 360582302177028394]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578860253457900, 360578893104644671⟩, ⟨241601569241612664, 243184565523589276⟩, true⟩

def words03 : List Nat := [360582302177934930, 360582302063127704, 360582302028447183, 360582302208707942, 360582302260632369, 360582302312715022, 360582302313632715, 360582302205195314, 360582301962115245, 360582301915487447]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585254710153892, 360585287570871367⟩, ⟨(-214631415884256709), (-213047739634638901)⟩, true⟩

def words04 : List Nat := [360582302016845699, 360582302017857472, 360582301970960806, 360582301825526173, 360582301679909851, 360582301441542225, 360582301500354466, 360582301628400510, 360582301629304652, 360582301659817078]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk713A

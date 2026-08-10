import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk187A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360452565284664131, 360452567302179443⟩, ⟨2485478063651538983, 2485503599413421109⟩, true⟩

def state01 : KState := ⟨⟨360548097923147801, 360548099942911907⟩, ⟨698698461307524643, 698724039133234853⟩, true⟩

def words00 : List Nat := [360585474826002914, 360585470569424539, 360585467746257297, 360585466730707283, 360585465715243416, 360585462149255630, 360585456787738867, 360585452211570069, 360585447635821092, 360585444894228489]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573064507938523, 360573066529980679⟩, ⟨231230855834849980, 231256476294115278⟩, true⟩

def words01 : List Nat := [360585442898566074, 360585438243090864, 360585433588067746, 360585431778952732, 360585431413462440, 360585429666146245, 360585427918991273, 360585424138293770, 360585420633893169, 360585419974227160]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360612419592782312, 360612421617070660⟩, ⟨(-505599605358595457), (-505573942839127319)⟩, true⟩

def words02 : List Nat := [360585420545183130, 360585422976357934, 360585423851516644, 360585424726608149, 360585424726811709, 360585423878295633, 360585426029387810, 360585428180295818, 360585428880953907, 360585430322273846]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360674693899764070, 360674695926310999⟩, ⟨(-1672256791926157118), (-1672231087092337794)⟩, true⟩

def words03 : List Nat := [360585434603727244, 360585438884797506, 360585442088157433, 360585446253147351, 360585447989023631, 360585449724733460, 360585453056110812, 360585457914922370, 360585462677019343, 360585467438658668]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360714652862732364, 360714654891554461⟩, ⟨(-2421858619720968672), (-2421832872239143796)⟩, true⟩

def words04 : List Nat := [360585470770170969, 360585471272840700, 360585474612077520, 360585477951029390, 360585479642619164, 360585482724819537, 360585484362064597, 360585485999159341, 360585490471429233, 360585497360103385]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk187A

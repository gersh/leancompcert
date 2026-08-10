import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk896A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583629752239388, 360583682504429377⟩, ⟨(-150113643735580007), (-146921844977708617)⟩, true⟩

def state01 : KState := ⟨⟨360576858424769855, 360576911189268016⟩, ⟨456577090477213287, 459769992106887305⟩, true⟩

def words00 : List Nat := [360582042771147328, 360582042728216958, 360582042597252898, 360582042591105024, 360582042584597823, 360582042546888605, 360582042490001501, 360582042318203377, 360582042146164674, 360582041978154378]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567961944792330, 360568014721449444⟩, ⟨1253923167694077599, 1257117158950332291⟩, true⟩

def words01 : List Nat := [360582041989083970, 360582042057516681, 360582042061918300, 360582042105993578, 360582042118429583, 360582042131208433, 360582042162590268, 360582042163883057, 360582042070995961, 360582041915813987]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577248329991511, 360577301118877593⟩, ⟨421575923254590999, 424771010528688881⟩, true⟩

def words02 : List Nat := [360582041760361637, 360582041559245156, 360582041437643035, 360582041325673622, 360582041213604139, 360582040993904001, 360582040700645798, 360582040532158732, 360582040363261174, 360582040279990264]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558661459732001, 360558714260933116⟩, ⟨2087660939356725969, 2090857130488187945⟩, true⟩

def words03 : List Nat := [360582040228280483, 360582040095869880, 360582039963214328, 360582040008331281, 360582040009437288, 360582039960903577, 360582039912229899, 360582039801251599, 360582039565732056, 360582039307011744]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573274655505862, 360573327468903716⟩, ⟨777647207000279062, 780844491507858616⟩, true⟩

def words04 : List Nat := [360582039047854648, 360582038830900248, 360582038659710212, 360582038426235296, 360582038192554330, 360582037927867099, 360582037743627980, 360582037658825485, 360582037573908705, 360582037390727563]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk896A

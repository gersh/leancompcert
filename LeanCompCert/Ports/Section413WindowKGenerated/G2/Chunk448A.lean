import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk448A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576361737111563, 360576374214979079⟩, ⟨304685698476956327, 305063461458710345⟩, true⟩

def state01 : KState := ⟨⟨360597186229085878, 360597198712733984⟩, ⟨(-628333280870219720), (-627955258889281854)⟩, true⟩

def words00 : List Nat := [360583183714902469, 360583184234855413, 360583184830809667, 360583185426852159, 360583185573919109, 360583185574532390, 360583185420592214, 360583185108745945, 360583184981706905, 360583185295071150]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601645429311658, 360601657918804113⟩, ⟨(-828181050063142109), (-827802766168823841)⟩, true⟩

def words01 : List Nat := [360583185295625006, 360583185289329577, 360583185569260989, 360583186358466982, 360583187020527478, 360583187682658424, 360583188095014972, 360583188095628209, 360583188423091902, 360583188835870470]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561014775294839, 360561027270570907⟩, ⟨992979435279728615, 993357978424410045⟩, true⟩

def words02 : List Nat := [360583189064728228, 360583189065341603, 360583188949679748, 360583188510806825, 360583188071854684, 360583187283593448, 360583186778051125, 360583186500382464, 360583186222655196, 360583185601564091]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604447952357333, 360604460453421581⟩, ⟨(-954400830970801313), (-954022028313905405)⟩, true⟩

def words03 : List Nat := [360583185107796533, 360583184992071504, 360583185138686077, 360583185142735081, 360583185143310653, 360583184668543821, 360583184193679033, 360583183862017484, 360583184314776397, 360583184789892358]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599310472890582, 360599322979805371⟩, ⟨(-724041513417514763), (-723662448394621081)⟩, true⟩

def words04 : List Nat := [360583185015551981, 360583185258231446, 360583185997426685, 360583186736769065, 360583187349363546, 360583187798591286, 360583187854304685, 360583187910073352, 360583187910578287, 360583188167908321]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk448A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk617A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360628977124195002, 360629001414380603⟩, ⟨(-2864222692237224367), (-2863210247780408291)⟩, true⟩

def state01 : KState := ⟨⟨360603512681205900, 360603536979623519⟩, ⟨(-1293075664067837392), (-1292062711655413038)⟩, true⟩

def words00 : List Nat := [360582597411706656, 360582597747903621, 360582598346497647, 360582598945335061, 360582599302015317, 360582599397249042, 360582599398019818, 360582599332932155, 360582599323277367, 360582599663559035]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567482684764210, 360567506991334472⟩, ⟨930550085909237967, 931563541462693133⟩, true⟩

def words01 : List Nat := [360582599988359293, 360582600313329015, 360582600506886526, 360582600529741435, 360582600530465517, 360582600486379838, 360582600659460342, 360582600660325745, 360582600617060357, 360582600373406130]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602604321176936, 360602628635914921⟩, ⟨(-1237379343249779218), (-1236365383543693294)⟩, true⟩

def words02 : List Nat := [360582600129568916, 360582599853754265, 360582599846788599, 360582599975036869, 360582599975835722, 360582599877205916, 360582599785004355, 360582599781796366, 360582600036549189, 360582600361894677]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582611039508971, 360582635362508995⟩, ⟨(-3108164266852369), (-2093694505327705)⟩, true⟩

def words03 : List Nat := [360582600528998157, 360582600696189242, 360582600855981216, 360582601146412347, 360582601369669577, 360582601593060932, 360582601651504894, 360582601652370563, 360582601450019502, 360582601451582620]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569110003730833, 360569134334881192⟩, ⟨830443132995185357, 831458105998709567⟩, true⟩

def words04 : List Nat := [360582601593839422, 360582601594705136, 360582601475782490, 360582601158209770, 360582600840503890, 360582600415589134, 360582600161072828, 360582599899553166, 360582599637954900, 360582599243480362]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk617A

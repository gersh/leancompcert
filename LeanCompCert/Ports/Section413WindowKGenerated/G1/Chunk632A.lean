import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk632A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497935841668825, 362497994646638264⟩, ⟨(-797268679710759374), (-794758413854370220)⟩, true⟩

def state01 : KState := ⟨⟨362490560925983305, 362490619750345085⟩, ⟨(-331217285906194976), (-328705794355359858)⟩, true⟩

def words00 : List Nat := [371285419753966853, 371285419756114096, 371285419622114238, 371285419592771103, 371285419606558093, 371285419608736256, 371285419538524643, 371285419467190235, 371285419529621125, 371285419614382115]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471799638327519, 362471858481992221⟩, ⟨854870626465038799, 857383338252492545⟩, true⟩

def words01 : List Nat := [371285419948371776, 371285420283204990, 371285420614813605, 371285420616961118, 371285420668755991, 371285420725126733, 371285420806689144, 371285420808837072, 371285420594440655, 371285420382312571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482147517190308, 362482206380063771⟩, ⟨200673861245608261, 203187787510135013⟩, true⟩

def words02 : List Nat := [371285420181898648, 371285420184266340, 371285420144262697, 371285420205048813, 371285420229592909, 371285420231741099, 371285419947763039, 371285419844675528, 371285419849096013, 371285419851319665]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483737523849563, 362483796406354173⟩, ⟨100139981461360646, 102655149098422280⟩, true⟩

def words03 : List Nat := [371285419802132402, 371285419705800014, 371285419706079756, 371285419708471219, 371285419734410785, 371285419786924714, 371285419842360257, 371285419844546177, 371285419692285404, 371285419669306394]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483296559503534, 362483355461129910⟩, ⟨128037199381701392, 130553576377184072⟩, true⟩

def words04 : List Nat := [371285419869460371, 371285419871609088, 371285419793002933, 371285419716731759, 371285419639693228, 371285419563102438, 371285419437674614, 371285419501587744, 371285419547048652, 371285419549293977]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk632A

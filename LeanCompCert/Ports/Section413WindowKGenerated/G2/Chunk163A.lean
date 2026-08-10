import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk163A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551217450711317, 360551218964431134⟩, ⟨510372522503107481, 510389226785010863⟩, true⟩

def state01 : KState := ⟨⟨360659730985051636, 360659732500713361⟩, ⟨(-1258989587622846303), (-1258972851678507593)⟩, true⟩

def words00 : List Nat := [360582531100864789, 360582536139364586, 360582539398098134, 360582542656467845, 360582542733252165, 360582542733457700, 360582540787247036, 360582540505195020, 360582542258211678, 360582546990831778]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607905121195582, 360607906638812617⟩, ⟨(-413567454068114289), (-413550686222679793)⟩, true⟩

def words01 : List Nat := [360582549822300260, 360582552653444012, 360582555992858990, 360582561203268830, 360582564260820425, 360582567318029918, 360582567318217994, 360582567164335328, 360582566523000718, 360582568075843272]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594895042302496, 360594896561855882⟩, ⟨(-201479229654591746), (-201462430198188796)⟩, true⟩

def words02 : List Nat := [360582571182008455, 360582571182214061, 360582570572865140, 360582568067284838, 360582565561973419, 360582562083665856, 360582560859714642, 360582561181201449, 360582561181384708, 360582560365040122]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360645184408057240, 360645185929554193⟩, ⟨(-1023297726917531990), (-1023280895713077774)⟩, true⟩

def words03 : List Nat := [360582560984176146, 360582561603293377, 360582565961173846, 360582566607225437, 360582566607418153, 360582563565003620, 360582560522922931, 360582557806540551, 360582561639517552, 360582565472072211]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614063079389938, 360614064602845195⟩, ⟨(-515308668684375895), (-515291805471372575)⟩, true⟩

def words04 : List Nat := [360582566884122094, 360582566884327899, 360582564623633872, 360582564660522787, 360582564660698062, 360582562174552789, 360582559185152110, 360582554306877537, 360582549429160471, 360582550211953423]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk163A

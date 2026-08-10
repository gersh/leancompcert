import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk611A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360639081418957608, 360639105220579876⟩, ⟨(-3460603380186723918), (-3459620933743626478)⟩, true⟩

def state01 : KState := ⟨⟨360601539683546701, 360601563493335028⟩, ⟨(-1166799997733689446), (-1165817052306728276)⟩, true⟩

def words00 : List Nat := [360582484646348103, 360582485227524117, 360582485682656720, 360582486138014662, 360582486395415721, 360582486396271614, 360582486386984339, 360582486243231947, 360582486139161322, 360582486452339026]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547850112136782, 360547873929979332⟩, ⟨2114513319014829521, 2115496756677134401⟩, true⟩

def words01 : List Nat := [360582486888240945, 360582487324291772, 360582487591194787, 360582487592050806, 360582487592228354, 360582487434828620, 360582487277188546, 360582487112238783, 360582486680556374, 360582486115134390]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585277341619570, 360585301167540924⟩, ⟨(-173202874761768329), (-172218943282970271)⟩, true⟩

def words02 : List Nat := [360582485549536773, 360582485251829056, 360582485119654885, 360582485103350757, 360582485086965720, 360582484836146872, 360582484507179650, 360582484219094398, 360582483930757624, 360582483956252332]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595277834898493, 360595301668984899⟩, ⟨(-784636141781835824), (-783651711133838202)⟩, true⟩

def words03 : List Nat := [360582483957028587, 360582483759852787, 360582483577606994, 360582483766447397, 360582483886617068, 360582484006922744, 360582484007692538, 360582484125136263, 360582484335474228, 360582484546086454]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594901728736183, 360594925570881166⟩, ⟨(-761610777831733514), (-760625854442113160)⟩, true⟩

def words04 : List Nat := [360582485023823813, 360582485385049860, 360582485589783859, 360582485794604854, 360582485818074810, 360582486007116308, 360582486377251188, 360582486747538005, 360582486880632216, 360582487084929308]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk611A

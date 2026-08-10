import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk518A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607984691492624, 360608001573111622⟩, ⟨(-1349968478258348386), (-1349377613099077978)⟩, true⟩

def state01 : KState := ⟨⟨360593039528139638, 360593056416581382⟩, ⟨(-575885952967514826), (-575294734355915146)⟩, true⟩

def words00 : List Nat := [360581952602156761, 360581952649483612, 360581953068626255, 360581953487970283, 360581953698923052, 360581953699640057, 360581953538896869, 360581953093104448, 360581952647191991, 360581952698560964]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589509115417951, 360589526010608292⟩, ⟨(-392893551227901230), (-392301982937122830)⟩, true⟩

def words01 : List Nat := [360581953215480831, 360581953732518119, 360581954003623311, 360581954285080410, 360581954401110582, 360581954517328190, 360581955005101079, 360581955388740599, 360581955535475000, 360581955682306308]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611425431845800, 360611442333811897⟩, ⟨(-1528836910040710923), (-1528244990596422657)⟩, true⟩

def words02 : List Nat := [360581955682900224, 360581955778504083, 360581956120670055, 360581956462960102, 360581956492303265, 360581956493020606, 360581956179807584, 360581956209546035, 360581956610696136, 360581957180320813]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591849943235270, 360591866852037711⟩, ⟨(-514161554432137210), (-513569280625987260)⟩, true⟩

def words03 : List Nat := [360581957511683192, 360581957843109032, 360581958299729645, 360581958983089529, 360581959407925711, 360581959832852220, 360581960024393981, 360581960025111501, 360581960036384296, 360581960228310816]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614230497283238, 360614247412852852⟩, ⟨(-1674485474981560386), (-1673892850331568832)⟩, true⟩

def words04 : List Nat := [360581960673350396, 360581961231656643, 360581961507690234, 360581961783790656, 360581961967032779, 360581962338544831, 360581963002652651, 360581963666872303, 360581964039873124, 360581964663237000]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk518A

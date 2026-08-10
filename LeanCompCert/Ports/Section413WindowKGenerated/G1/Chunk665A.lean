import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk665A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483687368061897, 362483752735010335⟩, ⟨113467767092430803, 116403676574951679⟩, true⟩

def state01 : KState := ⟨⟨362477947013731896, 362478012401145007⟩, ⟨495180399349339859, 498117669836067079⟩, true⟩

def words00 : List Nat := [371285503141628199, 371285503114101878, 371285502821996005, 371285502733396310, 371285502643651339, 371285502613067824, 371285502379329541, 371285502099945800, 371285501819656941, 371285501766200429]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471632209037071, 362471697616871332⟩, ⟨915290909275385906, 918229538079606952⟩, true⟩

def words01 : List Nat := [371285501746756316, 371285501840865081, 371285501934483777, 371285501936791396, 371285501842030839, 371285501800440064, 371285501829315964, 371285501831584528, 371285501633275818, 371285501428327731]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483819432344252, 362483884860537633⟩, ⟨104519193281830821, 107459176471693187⟩, true⟩

def words02 : List Nat := [371285501222395263, 371285501028968158, 371285500721434169, 371285500640469046, 371285500558823045, 371285500442435475, 371285500143806447, 371285500041044003, 371285500056993838, 371285500059342258]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485462798446490, 362485528247262321⟩, ⟨(-4787889293877076), (-1846533984520416)⟩, true⟩

def words03 : List Nat := [371285500036761378, 371285499994892005, 371285500133414582, 371285500231608649, 371285500338783130, 371285500446815541, 371285500553318340, 371285500555598665, 371285500493741257, 371285500496943202]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485129125750316, 362485194594806149⟩, ⟨17465482424596370, 20408184609155248⟩, true⟩

def words04 : List Nat := [371285500724456974, 371285500774442581, 371285500799529879, 371285500825411397, 371285500919640218, 371285500922164325, 371285501034013159, 371285501166361815, 371285501251861329, 371285501254229277]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk665A

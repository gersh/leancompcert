import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk519A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360598241187801568, 360598258137372299⟩, ⟨(-845347965012324023), (-844753576555771549)⟩, true⟩

def state01 : KState := ⟨⟨360577578255357767, 360577595211690132⟩, ⟨227041265169421303, 227636004588460237⟩, true⟩

def words00 : List Nat := [360581982169583842, 360581982170302261, 360581982080673842, 360581981776675256, 360581981472581583, 360581980911523831, 360581980631337989, 360581980676970404, 360581980677617779, 360581980416941307]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594460779877993, 360594477743000856⟩, ⟨(-649460729267249810), (-648865637320078396)⟩, true⟩

def words01 : List Nat := [360581980333047963, 360581980239212806, 360581980421032855, 360581980440298174, 360581980440960691, 360581980142212166, 360581979843337511, 360581980088830071, 360581980330130917, 360581980571580428]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360609456946060093, 360609473916027012⟩, ⟨(-1428300467323194650), (-1427705019998424280)⟩, true⟩

def words02 : List Nat := [360581980623353222, 360581980624075305, 360581980806008791, 360581981040867445, 360581981094766707, 360581981159213736, 360581981159855285, 360581980996683450, 360581981039790659, 360581981570029469]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557447160629501, 360557464137374485⟩, ⟨1272874301194702239, 1273470100538170765⟩, true⟩

def words03 : List Nat := [360581982156004004, 360581982742089819, 360581983044356606, 360581983175063382, 360581983175669622, 360581983006193920, 360581982956745825, 360581982957464819, 360581982708413541, 360581982237115305]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599596249594066, 360599613233124880⟩, ⟨(-916491319338812229), (-915895167506164365)⟩, true⟩

def words04 : List Nat := [360581981765659065, 360581981844096938, 360581982310813411, 360581982777649974, 360581982926897562, 360581982927618186, 360581982920419986, 360581982794461492, 360581982911542202, 360581983251651835]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk519A

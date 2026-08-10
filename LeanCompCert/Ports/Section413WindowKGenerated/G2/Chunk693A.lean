import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk693A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571011916776395, 360571042844650610⟩, ⟨808596982722615583, 810044721464778893⟩, true⟩

def state01 : KState := ⟨⟨360553977879162366, 360554008816259981⟩, ⟨1989112555610367846, 1990560933581768026⟩, true⟩

def words00 : List Nat := [360582731633794276, 360582731586778204, 360582731331684371, 360582730946088174, 360582730560343504, 360582730096041088, 360582729736263133, 360582729372681004, 360582729009013986, 360582728495001603]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591538061071965, 360591569007425925⟩, ⟨(-614429098314806906), (-612980078739125252)⟩, true⟩

def words01 : List Nat := [360582728081440430, 360582727700534842, 360582727319350354, 360582727146034928, 360582726978793338, 360582726634143847, 360582726289310827, 360582726152424542, 360582726247051983, 360582726375629801]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593069842255947, 360593100797965106⟩, ⟨(-720688914838292434), (-719239246714247166)⟩, true⟩

def words02 : List Nat := [360582726376519097, 360582726365124456, 360582726560035687, 360582726755229289, 360582726840187337, 360582726856904313, 360582726857786609, 360582726770225243, 360582726682465395, 360582726805858917]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360554856245420383, 360554887210360796⟩, ⟨1928844014190017910, 1930294322363293686⟩, true⟩

def words03 : List Nat := [360582726952221266, 360582727098765088, 360582727099645233, 360582727085461012, 360582726863338579, 360582726502507431, 360582726141387766, 360582725987984098, 360582725717578119, 360582725317115387]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573907740012051, 360573938714232264⟩, ⟨607781274999341000, 609232226678120800⟩, true⟩

def words04 : List Nat := [360582724916441985, 360582724723595637, 360582724755743929, 360582724807980363, 360582724808895298, 360582724660331628, 360582724303870514, 360582724072583730, 360582723841029673, 360582723605748892]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk693A

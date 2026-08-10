import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk866A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488591977780583, 362488705123229651⟩, ⟨(-309824358819475475), (-303208427898542685)⟩, true⟩

def state01 : KState := ⟨⟨362485037079250006, 362485150251866001⟩, ⟨(-1987045557890367), 4631238161422323⟩, true⟩

def words00 : List Nat := [371285203954420411, 371285203957441179, 371285203890955003, 371285203894493900, 371285203937220076, 371285203940247057, 371285203855689686, 371285203772227295, 371285203720755093, 371285203724192077]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483874714270835, 362483987914022882⟩, ⟨98705448576682166, 105326082686821488⟩, true⟩

def words01 : List Nat := [371285203780143042, 371285203837874602, 371285203894764480, 371285203897800355, 371285203861119343, 371285203836827285, 371285203886632012, 371285203889702149, 371285203880402009, 371285203869722338]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487642246925390, 362487755473612569⟩, ⟨(-227655149407794782), (-221032182036525878)⟩, true⟩

def words02 : List Nat := [371285203910880337, 371285203914201126, 371285203977738530, 371285204056005014, 371285204084101733, 371285204087115175, 371285203937246494, 371285203922053131, 371285204019701594, 371285204052273366]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482679243772028, 362482792498000505⟩, ⟨202347407227460650, 208972760632976498⟩, true⟩

def words03 : List Nat := [371285204073411573, 371285204095678006, 371285204218019292, 371285204275059454, 371285204371637384, 371285204469363071, 371285204566215016, 371285204569228728, 371285204488360076, 371285204464305134]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470344499438124, 362470457780492745⟩, ⟨1271110039772790804, 1277737717537947706⟩, true⟩

def words04 : List Nat := [371285204506286491, 371285204509300286, 371285204401822731, 371285204294227856, 371285204185520495, 371285204098698004, 371285203961910953, 371285203894815944, 371285203826683354, 371285203743764966]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk866A

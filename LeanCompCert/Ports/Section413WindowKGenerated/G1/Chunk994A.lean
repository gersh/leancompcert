import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk994A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484512778282952, 362484663435668360⟩, ⟨58769349945248167, 68879815115385063⟩, true⟩

def state01 : KState := ⟨⟨362490832611054384, 362490983299674498⟩, ⟨(-569413224367978431), (-559299654306260519)⟩, true⟩

def words00 : List Nat := [371285356481229933, 371285356528804503, 371285356665388920, 371285356803362115, 371285356923640996, 371285356935338207, 371285356957557710, 371285356981589270, 371285357104986099, 371285357165199377]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496754360174237, 362496905080596931⟩, ⟨(-1158117705530704463), (-1148000973813718823)⟩, true⟩

def words01 : List Nat := [371285357223515082, 371285357282969873, 371285357431505637, 371285357545430869, 371285357673784625, 371285357803518178, 371285357934423175, 371285357975554905, 371285358094070387, 371285358214504117]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483169819220094, 362483320570815004⟩, ⟨192525215062414816, 202645046079669308⟩, true⟩

def words02 : List Nat := [371285358374624454, 371285358400973138, 371285358426415765, 371285358453082524, 371285358484827258, 371285358488679919, 371285358534446647, 371285358597151704, 371285358634640552, 371285358638260239]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496489838682904, 362496640621896341⟩, ⟨(-1131951722236483658), (-1121828747229302114)⟩, true⟩

def words03 : List Nat := [371285358700825543, 371285358785771410, 371285358932807808, 371285358958753420, 371285358961505391, 371285358961182419, 371285359022272143, 371285359038403562, 371285359154224818, 371285359271676319]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491600932660261, 362491751747462007⟩, ⟨(-645785600570410809), (-635659484263630213)⟩, true⟩

def words04 : List Nat := [371285359378451105, 371285359402140889, 371285359518097726, 371285359635828510, 371285359782369575, 371285359825313440, 371285359867258836, 371285359910419261, 371285359993935733, 371285360062267654]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk994A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk620A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491544431887017, 362491600939520577⟩, ⟨(-387601486378442446), (-385235038661746784)⟩, true⟩

def state01 : KState := ⟨⟨362490899772017546, 362490956298631595⟩, ⟨(-347671073911845742), (-345303449307600850)⟩, true⟩

def words00 : List Nat := [371285387673485657, 371285387675590967, 371285387575306586, 371285387657134020, 371285387816317728, 371285387818458981, 371285387792695718, 371285387719908707, 371285387783872273, 371285387876104824]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489950431492395, 362490006977059804⟩, ⟨(-288748935801348990), (-286380135805647010)⟩, true⟩

def words01 : List Nat := [371285388227632597, 371285388579987024, 371285388882826297, 371285388884930347, 371285388916025591, 371285388966306401, 371285389275732799, 371285389353714959, 371285389429757691, 371285389506593259]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486979773192567, 362487036337561957⟩, ⟨(-104414246584047437), (-102044280389943335)⟩, true⟩

def words02 : List Nat := [371285389814836671, 371285389994568287, 371285390338772871, 371285390683834208, 371285390984533864, 371285390986638117, 371285391000488488, 371285391062845959, 371285391255899821, 371285391284598279]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483039472442007, 362483096056013686⟩, ⟨140019897907571950, 142391055313568364⟩, true⟩

def words03 : List Nat := [371285391286176176, 371285391280832245, 371285391361486482, 371285391363846412, 371285391420338963, 371285391482255704, 371285391533113060, 371285391535217683, 371285391239547840, 371285391205196691]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474985381939020, 362475041984279498⟩, ⟨639721217948773866, 642093539867189654⟩, true⟩

def words04 : List Nat := [371285391239922817, 371285391242027850, 371285391006796230, 371285390771132273, 371285390534689014, 371285390377354464, 371285390091031968, 371285390065663749, 371285390039524898, 371285389986533603]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk620A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk762A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571938703903662, 360571976379588485⟩, ⟨775429385019847015, 777368422501623899⟩, true⟩

def state01 : KState := ⟨⟨360587335054660846, 360587372740584911⟩, ⟨(-397827692594395943), (-395887874829708837)⟩, true⟩

def words00 : List Nat := [360582177939784239, 360582177953525452, 360582177954502147, 360582177881500553, 360582177808323884, 360582177692049003, 360582177850634830, 360582178016559946, 360582178042244653, 360582178111530973]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595879660692028, 360595917356866556⟩, ⟨(-1049035916654369821), (-1047095317650756953)⟩, true⟩

def words01 : List Nat := [360582178238952338, 360582178366699073, 360582178666046051, 360582178849055253, 360582178885484539, 360582178922016168, 360582179103725983, 360582179371965861, 360582179553095846, 360582179734457368]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581331734407950, 360581369440955004⟩, ⟨59758987441054784, 61700377086957902⟩, true⟩

def words02 : List Nat := [360582179827038248, 360582179839415288, 360582179847620167, 360582179856128247, 360582179857038495, 360582179821417808, 360582179613967262, 360582179320495115, 360582179026817886, 360582178838529279]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553156347455151, 360553194064215548⟩, ⟨2207809605832902548, 2209751774094748354⟩, true⟩

def words03 : List Nat := [360582178990017084, 360582179152331514, 360582179228394236, 360582179229480937, 360582179191479338, 360582179087549887, 360582178983319794, 360582178875343111, 360582178595601775, 360582178216551524]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573606654570159, 360573644381591001⟩, ⟨648536040336548562, 650478990903254448⟩, true⟩

def words04 : List Nat := [360582177837271779, 360582177421438839, 360582177114700241, 360582176979992362, 360582176845193482, 360582176540743091, 360582176118994825, 360582175773402914, 360582175427488962, 360582175253602847]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk762A

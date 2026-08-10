import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk645A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496860760250367, 362496922107402526⟩, ⟨(-737390942438856678), (-734718351941622102)⟩, true⟩

def state01 : KState := ⟨⟨362486891653559154, 362486953020233255⟩, ⟨(-94316587771534964), (-91642738005651812)⟩, true⟩

def words00 : List Nat := [371285531684608039, 371285531747852487, 371285531810886632, 371285531874678288, 371285531926913560, 371285531929343212, 371285532065640315, 371285532243744473, 371285532420565720, 371285532444858426]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497236870455285, 362497298257029136⟩, ⟨(-761697168378252260), (-759022034783763404)⟩, true⟩

def words01 : List Nat := [371285532667520624, 371285532891415950, 371285533354321798, 371285533497796588, 371285533531139810, 371285533565126799, 371285533809477561, 371285533934993849, 371285534118852484, 371285534303668467]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492165615485439, 362492227021876400⟩, ⟨(-434541204103474073), (-431864791810131143)⟩, true⟩

def words02 : List Nat := [371285534466043966, 371285534468239134, 371285534369933495, 371285534432076141, 371285534525810167, 371285534528058899, 371285534489597715, 371285534439630855, 371285534553953708, 371285534660192712]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480336384634800, 362480397810796837⟩, ⟨328919412134182260, 331597100356634978⟩, true⟩

def words03 : List Nat := [371285534965511494, 371285535271711360, 371285535531070107, 371285535533266714, 371285535566120337, 371285535620899350, 371285535797960648, 371285535800159978, 371285535741966701, 371285535664846367]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482375846684259, 362482437292501406⟩, ⟨197349656666517697, 200028613530097865⟩, true⟩

def words04 : List Nat := [371285535725262458, 371285535760549367, 371285535929392542, 371285536099150642, 371285536241471361, 371285536243667967, 371285536096904004, 371285536050794484, 371285536106856454, 371285536109132392]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk645A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk965A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497716277783521, 362497857950694997⟩, ⟨(-1222223460034589820), (-1212993093729688002)⟩, true⟩

def state01 : KState := ⟨⟨362484571456680453, 362484713160132255⟩, ⟨46319375384126444, 55552688989773718⟩, true⟩

def words00 : List Nat := [371285288334605121, 371285288390208199, 371285288491615813, 371285288594790998, 371285288728467614, 371285288734955185, 371285288740962023, 371285288748064235, 371285288772154282, 371285288776016514]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484618848215454, 362484760582201521⟩, ⟨41791404762406012, 51027665379419982⟩, true⟩

def words01 : List Nat := [371285288860418002, 371285288952231104, 371285289040069409, 371285289049414902, 371285289082389549, 371285289117110970, 371285289257504600, 371285289260890244, 371285289258362580, 371285289256728867]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496223179277403, 362496364943602719⟩, ⟨(-1078315586096124559), (-1069076396981069267)⟩, true⟩

def words02 : List Nat := [371285289345635701, 371285289388015397, 371285289473475556, 371285289560243294, 371285289621999027, 371285289625394236, 371285289643670385, 371285289709496238, 371285289871175886, 371285289989474190]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499326671259472, 362499468466373044⟩, ⟨(-1377908625170858134), (-1368666463907381932)⟩, true⟩

def words03 : List Nat := [371285290097628215, 371285290206890587, 371285290397662924, 371285290545596613, 371285290718832689, 371285290893418077, 371285291046044811, 371285291117453052, 371285291266608241, 371285291417617517]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487076120735751, 362487217945988692⟩, ⟨(-195165426563143328), (-185920355486575574)⟩, true⟩

def words04 : List Nat := [371285291645803810, 371285291731997170, 371285291803215975, 371285291875660442, 371285291978877031, 371285292030035628, 371285292121119992, 371285292213535411, 371285292304410354, 371285292327864731]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk965A

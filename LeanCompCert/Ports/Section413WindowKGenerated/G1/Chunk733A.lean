import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk733A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471669448909838, 362471749473597357⟩, ⟨989898617576124433, 993859973888006147⟩, true⟩

def state01 : KState := ⟨⟨362483643041253023, 362483723088479052⟩, ⟨112212564576914991, 116175573074191889⟩, true⟩

def words00 : List Nat := [371285308089431654, 371285308039729006, 371285307981465426, 371285308047249339, 371285308085822618, 371285308088341222, 371285307878761862, 371285307792799993, 371285307802459838, 371285307805067160]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487791035027047, 362487871105257773⟩, ⟨(-191908631860511114), (-187943936776499966)⟩, true⟩

def words01 : List Nat := [371285307785366356, 371285307728284344, 371285307779044441, 371285307798466604, 371285307818706557, 371285307839874175, 371285307860787831, 371285307863350842, 371285307764171769, 371285307802291686]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476958390725281, 362477038483372099⟩, ⟨602385311520011015, 606351650270151409⟩, true⟩

def words02 : List Nat := [371285307907238855, 371285307909758534, 371285307793155166, 371285307676205571, 371285307558345959, 371285307446455100, 371285307272697715, 371285307280612806, 371285307288213671, 371285307290821577]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486651709192210, 362486731824619702⟩, ⟨(-108435266690094216), (-104467257320200510)⟩, true⟩

def words03 : List Nat := [371285307252754341, 371285307328807429, 371285307525811072, 371285307528331853, 371285307511355288, 371285307464258273, 371285307432162088, 371285307434946089, 371285307397790839, 371285307420025816]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482968036128509, 362483048174319452⟩, ⟨161691252132402980, 165660931086171762⟩, true⟩

def words04 : List Nat := [371285307429329575, 371285307431849406, 371285307193306767, 371285307118889272, 371285307043189917, 371285307024898410, 371285306911423767, 371285306784941810, 371285306670815999, 371285306673720764]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk733A

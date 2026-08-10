import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk514A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360531420780475669, 360531437391882014⟩, ⟨2593708153595101633, 2594285075726185073⟩, true⟩

def state01 : KState := ⟨⟨360551119146434041, 360551135764562304⟩, ⟨1581027835608154138, 1581605103278258328⟩, true⟩

def words00 : List Nat := [360581908882821650, 360581907888246684, 360581907128273951, 360581906426389544, 360581905724477871, 360581904660401552, 360581903218604337, 360581902154527396, 360581901090259713, 360581900306543986]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557491249890226, 360557507874785615⟩, ⟨1253406432878826224, 1253984048480086050⟩, true⟩

def words01 : List Nat := [360581899708773508, 360581898921880395, 360581898134881723, 360581897725462432, 360581897654334149, 360581897274859921, 360581896895329208, 360581896286925290, 360581895435935768, 360581894962465119]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573029048713389, 360573045680317926⟩, ⟨454392883774799658, 454970844393483546⟩, true⟩

def words02 : List Nat := [360581894488776946, 360581894392490908, 360581894306884756, 360581893999154733, 360581893691326928, 360581893052839872, 360581892601520203, 360581892527531656, 360581892453475200, 360581892089891978]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360613344395267014, 360613361033580563⟩, ⟨(-1619297964342794523), (-1618719658645955053)⟩, true⟩

def words03 : List Nat := [360581892123582498, 360581892329479066, 360581892700638049, 360581892701349543, 360581892695361617, 360581892362651983, 360581892073421726, 360581892308953019, 360581892921284139, 360581893533752684]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604870692284905, 360604887337384891⟩, ⟨(-1183559521195004012), (-1182980866371239436)⟩, true⟩

def words04 : List Nat := [360581893907059163, 360581894209565776, 360581894502372115, 360581894795373044, 360581894994156181, 360581894994868412, 360581894994891085, 360581894708294420, 360581894511167220, 360581894958881631]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk514A

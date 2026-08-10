import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk184A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360558496274619506, 360558498225038190⟩, ⟨485948984457371304, 485973275550597802⟩, true⟩

def state01 : KState := ⟨⟨360615949938005247, 360615951890638813⟩, ⟨(-571582056635396800), (-571557724777205138)⟩, true⟩

def words00 : List Nat := [360584909893218616, 360584912888346047, 360584914250581356, 360584915612709009, 360584915612927013, 360584914461463503, 360584910379916063, 360584908317825449, 360584906255889496, 360584907529942642]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585411358915056, 360585413313781007⟩, ⟨(-9139588033968666), (-9115215066539160)⟩, true⟩

def words01 : List Nat := [360584907530152537, 360584906968377949, 360584908788282758, 360584913395376049, 360584916523915385, 360584919652153048, 360584920505948024, 360584920506182706, 360584918459275784, 360584918486406460]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583513218704554, 360583515175780436⟩, ⟨25521742559868183, 25546156245059365⟩, true⟩

def words02 : List Nat := [360584919151571773, 360584919151806531, 360584918056828503, 360584915012694938, 360584911968851056, 360584906808726991, 360584903595102534, 360584903321421578, 360584903047744079, 360584901293862100]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360708534524578404, 360708536483872890⟩, ⟨(-2279578957897006845), (-2279554503311603527)⟩, true⟩

def words03 : List Nat := [360584901218849505, 360584901034646710, 360584903603406369, 360584905555915519, 360584905556131867, 360584904996032659, 360584905917580862, 360584909686796185, 360584916391259419, 360584923095048445]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360633388058123705, 360633390019657478⟩, ⟨(-893885560064112964), (-893861064175691138)⟩, true⟩

def words04 : List Nat := [360584928335401983, 360584930654570993, 360584935908218710, 360584941161365478, 360584943673114665, 360584944925465175, 360584944925676966, 360584943630806739, 360584942336032452, 360584944891253831]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk184A

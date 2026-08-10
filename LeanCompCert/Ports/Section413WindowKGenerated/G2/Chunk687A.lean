import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk687A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576529211944494, 360576559585555999⟩, ⟨428161117517720282, 429570611880311968⟩, true⟩

def state01 : KState := ⟨⟨360558718087200809, 360558748469959097⟩, ⟨1651798270590846783, 1653208393383107007⟩, true⟩

def words00 : List Nat := [360582812342662491, 360582812243664038, 360582811932976725, 360582811516564013, 360582811100021137, 360582810502644125, 360582810071794487, 360582809805528243, 360582809539164247, 360582809136432436]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588138233225149, 360588168625169028⟩, ⟨(-369749868784421199), (-368339114805329849)⟩, true⟩

def words01 : List Nat := [360582808787046173, 360582808649369631, 360582808584025696, 360582808680478737, 360582808681384163, 360582808598126008, 360582808514689181, 360582808546604574, 360582808625402825, 360582808704405283]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588651129250705, 360588681530446040⟩, ⟨(-405165335649697865), (-403753945865130313)⟩, true⟩

def words02 : List Nat := [360582808705271149, 360582808678457387, 360582808439975583, 360582808294976044, 360582808149712718, 360582807950771775, 360582807758406616, 360582807447467541, 360582807136344769, 360582807122306116]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360542301073541223, 360542331483900277⟩, ⟨2780715548230176915, 2782127567883981967⟩, true⟩

def words03 : List Nat := [360582807166097384, 360582807210067623, 360582807210956929, 360582807092732939, 360582806762949302, 360582806336754993, 360582805910288001, 360582805695267501, 360582805268760574, 360582804680989076]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574062978564124, 360574093398102030⟩, ⟨597256738406636130, 598669389058282664⟩, true⟩

def words04 : List Nat := [360582804092997168, 360582803651787820, 360582803353068833, 360582803265764712, 360582803178383003, 360582802910701304, 360582802524344524, 360582802051431753, 360582801578244742, 360582801316488333]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk687A

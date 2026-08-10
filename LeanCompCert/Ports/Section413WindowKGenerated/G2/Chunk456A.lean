import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk456A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360600429902552231, 360600442848880905⟩, ⟨(-785172041313383130), (-784773103301855696)⟩, true⟩

def state01 : KState := ⟨⟨360591192956451266, 360591205908660486⟩, ⟨(-363967668529642365), (-363568462335031533)⟩, true⟩

def words00 : List Nat := [360583233951995061, 360583234204046097, 360583234204608498, 360583234203903549, 360583234203102897, 360583233906304098, 360583234258571451, 360583234610942863, 360583234663498525, 360583234838911193]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572550207289654, 360572563165406999⟩, ⟨486489665545836043, 486889141239584159⟩, true⟩

def words01 : List Nat := [360583235173594462, 360583235508463114, 360583236323030346, 360583236658267825, 360583236658844125, 360583236586547461, 360583236514140656, 360583236192353253, 360583236111147302, 360583235877841011]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564091951627435, 360564104915703435⟩, ⟨872167877479686251, 872567625034998109⟩, true⟩

def words02 : List Nat := [360583235644460389, 360583235087040362, 360583234050269315, 360583233317292972, 360583232584184076, 360583231685055889, 360583230801747834, 360583229610511349, 360583228419201554, 360583227589931684]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360528129691748307, 360528142661717997⟩, ⟨2513397444216675988, 2513797460730828142⟩, true⟩

def words03 : List Nat := [360583227231856049, 360583227292970724, 360583227293537751, 360583226933843932, 360583226095054660, 360583225134179477, 360583224173163462, 360583223533250574, 360583222690436493, 360583221484258112]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566264307353239, 360566277283223839⟩, ⟨772745350210036167, 773145636071122967⟩, true⟩

def words04 : List Nat := [360583220277979966, 360583219551241873, 360583219064721561, 360583218717404313, 360583218370055159, 360583217560365562, 360583216501560555, 360583215430845785, 360583214359988402, 360583213660793853]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk456A

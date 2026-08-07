import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk456

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

def state06 : KState := ⟨⟨360571635841420940, 360571648823244129⟩, ⟨527488511440010308, 527889069066367356⟩, true⟩

def words05 : List Nat := [360583213290354346, 360583212679488867, 360583212068530519, 360583211893843340, 360583211894367745, 360583211735112777, 360583211575800555, 360583211109765262, 360583210378173042, 360583210125676595]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566466966583329, 360566479954306671⟩, ⟨763410859910326909, 763811686967248683⟩, true⟩

def words06 : List Nat := [360583209872996174, 360583209360040570, 360583208762588091, 360583207900728715, 360583207038805143, 360583206055077445, 360583205392315857, 360583205208438207, 360583205024492085, 360583204536898466]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360615783959005363, 360615796952634243⟩, ⟨(-1489159153506047135), (-1488758056714626741)⟩, true⟩

def words07 : List Nat := [360583204179076348, 360583204187638725, 360583204674626181, 360583204897321171, 360583204897914878, 360583204658517240, 360583204657555697, 360583205212239506, 360583205926226469, 360583206640322459]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597265745064362, 360597278744660387⟩, ⟨(-643191813964962782), (-642790444564998872)⟩, true⟩

def words08 : List Nat := [360583207114016974, 360583207801974565, 360583208563462480, 360583209325104311, 360583209964735709, 360583210291912081, 360583210310826161, 360583210329807693, 360583210330322908, 360583210537692604]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590886842020790, 360590899847514766⟩, ⟨(-351591505017216813), (-351189866110113313)⟩, true⟩

def words09 : List Nat := [360583211324330459, 360583212111053697, 360583212657023542, 360583213311810696, 360583213578267412, 360583213844888064, 360583214589419700, 360583214998365638, 360583215167082226, 360583215335882415]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk456

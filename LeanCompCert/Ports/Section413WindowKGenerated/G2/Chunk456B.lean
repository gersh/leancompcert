import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk456A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk456B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk456A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk456B

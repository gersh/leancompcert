import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk445A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk445B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk445A

def state06 : KState := ⟨⟨360554393801358259, 360554406140436573⟩, ⟨1284139490441978807, 1284511052311763339⟩, true⟩

def words05 : List Nat := [360583231404001409, 360583232515576920, 360583233374356249, 360583233730392132, 360583233730911986, 360583233674779463, 360583233728215070, 360583233728824346, 360583233336383790, 360583232690084504]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574425722329784, 360574438067165411⟩, ⟨391496163105232681, 391867981550260341⟩, true⟩

def words06 : List Nat := [360583232043679619, 360583231474567530, 360583231608941463, 360583231927906738, 360583231928468562, 360583231822029764, 360583231212858587, 360583230898710088, 360583230584399520, 360583230258808900]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577129244130965, 360577141594771628⟩, ⟨270950153224575664, 271322230427861950⟩, true⟩

def words07 : List Nat := [360583230062089265, 360583229591520063, 360583229120851825, 360583228925676635, 360583228926187356, 360583228914341514, 360583228902427268, 360583228556473534, 360583227917915949, 360583227782084950]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579855469118502, 360579867825507032⟩, ⟨149266596400696072, 149638929872194014⟩, true⟩

def words08 : List Nat := [360583227907210144, 360583227907819717, 360583227667321359, 360583226960569272, 360583226253749797, 360583225302011156, 360583224600195991, 360583224400849701, 360583224201445776, 360583223710904480]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585276052197299, 360585288414337102⟩, ⟨(-92543089753715147), (-92170499803799937)⟩, true⟩

def words09 : List Nat := [360583223636139901, 360583223509726543, 360583223474135044, 360583223494946556, 360583223495514059, 360583223084860945, 360583222674118804, 360583222092147897, 360583221810570492, 360583221857537842]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk445B

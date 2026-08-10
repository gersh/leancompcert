import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk842A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604871710829423, 360604918072586582⟩, ⟨(-1896046028999189222), (-1893409750696838240)⟩, true⟩

def state01 : KState := ⟨⟨360578770573243143, 360578816946529247⟩, ⟨301645126920631589, 304282376016746009⟩, true⟩

def words00 : List Nat := [360582431447037554, 360582431465348445, 360582431466343982, 360582431438239798, 360582431409810246, 360582431289521163, 360582431072504497, 360582430785056091, 360582430497380384, 360582430322328045]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568782830326312, 360568829214991645⟩, ⟨1142846128530762179, 1145484335928547755⟩, true⟩

def words01 : List Nat := [360582430378362331, 360582430477535179, 360582430505297682, 360582430550580970, 360582430560157077, 360582430570063768, 360582430571058286, 360582430545258760, 360582430471602718, 360582430311357456]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590019611888621, 360590066007963661⟩, ⟨(-645775119323239739), (-643135950942319121)⟩, true⟩

def words02 : List Nat := [360582430150841785, 360582430181772804, 360582430373820898, 360582430566117601, 360582430639551342, 360582430647923226, 360582430648914781, 360582430563895214, 360582430532997872, 360582430624898729]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601461745697534, 360601508153316252⟩, ⟨(-1609668416477156013), (-1607028275716930667)⟩, true⟩

def words03 : List Nat := [360582430626005284, 360582430607167284, 360582430680533095, 360582430857108701, 360582430949953075, 360582431042989800, 360582431053672212, 360582431140578374, 360582431368016118, 360582431595871339]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597422545641271, 360597468964637882⟩, ⟨(-1269396435596097706), (-1266755336305768930)⟩, true⟩

def words04 : List Nat := [360582431922392254, 360582432147739635, 360582432302423695, 360582432457236099, 360582432496825273, 360582432622521810, 360582432888620650, 360582433154944982, 360582433291736797, 360582433471453163]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk842A

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk491A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk491B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk491A

def state06 : KState := ⟨⟨360575496743735868, 360575511883714693⟩, ⟨313143629116515233, 313646554706254409⟩, true⟩

def words05 : List Nat := [360581894968051335, 360581894689012132, 360581894409789588, 360581894076920454, 360581893758056596, 360581893093217068, 360581892428274902, 360581892176050326, 360581892129859620, 360581892000775439]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590826841746797, 360590841988186194⟩, ⟨(-440798588211463040), (-440295344988479544)⟩, true⟩

def words06 : List Nat := [360581891871609261, 360581891420402825, 360581890699878123, 360581890308424122, 360581889916804760, 360581889422750516, 360581888984002297, 360581888330465785, 360581887676814441, 360581887617825850]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567157986510693, 360567173139324045⟩, ⟨723219971014135220, 723723527677002796⟩, true⟩

def words07 : List Nat := [360581888212755846, 360581888807792888, 360581889132855541, 360581889269227636, 360581889269805182, 360581889127405571, 360581889253872456, 360581889254550246, 360581889247687000, 360581888949158877]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573927635916896, 360573942795131330⟩, ⟨390269675780082872, 390773547280643082⟩, true⟩

def words08 : List Nat := [360581888650494552, 360581888207484984, 360581888276055760, 360581888470393542, 360581888471024162, 360581888317163007, 360581887750215989, 360581887490130419, 360581887229866233, 360581886961573303]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587516170059109, 360587531335731012⟩, ⟨(-278251759400573337), (-277747570225768349)⟩, true⟩

def words09 : List Nat := [360581886800682001, 360581886388379438, 360581885975955810, 360581886186887414, 360581886296299999, 360581886405830683, 360581886406435813, 360581886240953072, 360581886059139326, 360581886174652462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk491B

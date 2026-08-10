import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk783A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk783B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk783A

def state06 : KState := ⟨⟨360593340988129746, 360593380917903067⟩, ⟨(-873217662891099753), (-871104417259427539)⟩, true⟩

def words05 : List Nat := [360582263896439135, 360582263947980467, 360582263948893690, 360582264024764984, 360582264064249635, 360582264103918034, 360582264104915089, 360582264076338338, 360582264219111876, 360582264362253453]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592881197392827, 360592921137699916⟩, ⟨(-837257469088315297), (-835143397978006279)⟩, true⟩

def words06 : List Nat := [360582264580728765, 360582264636932953, 360582264637939415, 360582264612032315, 360582264585946950, 360582264447607251, 360582264547478569, 360582264679382124, 360582264719567810, 360582264856703400]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602232004632009, 360602271955518438⟩, ⟨(-1570100052400911611), (-1567985152136059405)⟩, true⟩

def words07 : List Nat := [360582265126090927, 360582265395833153, 360582265800551083, 360582266083985584, 360582266214562692, 360582266345212970, 360582266523927657, 360582266784297724, 360582267040451508, 360582267296836665]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603531771338221, 360603571732896502⟩, ⟨(-1672102277424043294), (-1669986540649509044)⟩, true⟩

def words08 : List Nat := [360582267472136525, 360582267485141535, 360582267623369244, 360582267761923785, 360582267833329808, 360582267990086913, 360582268013824326, 360582268037679277, 360582268165576992, 360582268438632499]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578145469338717, 360578185441449441⟩, ⟨318136875817676138, 320253439851759774⟩, true⟩

def words09 : List Nat := [360582268849946003, 360582269261463834, 360582269547697399, 360582269764265811, 360582269940089129, 360582270116205068, 360582270317506711, 360582270356668652, 360582270357676407, 360582270306753673]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk783B

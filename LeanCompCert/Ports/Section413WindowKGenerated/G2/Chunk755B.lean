import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk755A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk755B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk755A

def state06 : KState := ⟨⟨360604068117750006, 360604105138549016⟩, ⟨(-1656826769663824297), (-1654937425190293825)⟩, true⟩

def words05 : List Nat := [360582201894696488, 360582201933569343, 360582202147097524, 360582202261169127, 360582202262172584, 360582202212764551, 360582202287618269, 360582202551490537, 360582202842236659, 360582203133213059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568213057517272, 360568250088562556⟩, ⟨1052434517246895771, 1054324635979655443⟩, true⟩

def words06 : List Nat := [360582203328868771, 360582203349722563, 360582203363046720, 360582203376695051, 360582203377614186, 360582203227807555, 360582202902983093, 360582202490637119, 360582202078100251, 360582201717991955]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566310829669028, 360566347870855351⟩, ⟨1196244740046860998, 1198135625188148550⟩, true⟩

def words07 : List Nat := [360582201534246142, 360582201525620394, 360582201516868900, 360582201417110048, 360582201223627173, 360582200986114648, 360582200748292099, 360582200685551829, 360582200628115459, 360582200419481815]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605795483877810, 360605832535227209⟩, ⟨(-1788219419896106528), (-1786327766579919232)⟩, true⟩

def words08 : List Nat := [360582200210615677, 360582200029331507, 360582200115193534, 360582200246181497, 360582200247174591, 360582200229357731, 360582200340228887, 360582200465047487, 360582200734052064, 360582201047793786]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580719347655039, 360580756409285992⟩, ⟨107417916625748391, 109310347174333687⟩, true⟩

def words09 : List Nat := [360582201241722070, 360582201435760259, 360582201625608346, 360582201918069317, 360582202114174753, 360582202310446198, 360582202407710311, 360582202408787145, 360582202331211183, 360582202313349145]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk755B

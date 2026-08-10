import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk812A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk812B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk812A

def state06 : KState := ⟨⟨360609224748241147, 360609267809875349⟩, ⟨(-2201576025098262487), (-2199212796402220935)⟩, true⟩

def words05 : List Nat := [360582201628883542, 360582201973674763, 360582202442025551, 360582202759506391, 360582202947310625, 360582203135220910, 360582203307607649, 360582203571193299, 360582203905192479, 360582204239449164]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590218603819341, 360590261676560789⟩, ⟨(-657182038432600676), (-654817907110435896)⟩, true⟩

def words06 : List Nat := [360582204497362984, 360582204667578646, 360582204735687552, 360582204804113021, 360582204834485847, 360582204835649395, 360582204750823978, 360582204579209829, 360582204407369207, 360582204461722650]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550412771003852, 360550455854695367⟩, ⟨2578131374071161937, 2580496395361830067⟩, true⟩

def words07 : List Nat := [360582204669027462, 360582204876549937, 360582205008296012, 360582205009459640, 360582204990135638, 360582204931259392, 360582204872056013, 360582204750235081, 360582204477309424, 360582204087906020]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579506982957394, 360579550077634848⟩, ⟨213262245872215831, 215628160153921963⟩, true⟩

def words08 : List Nat := [360582203698248357, 360582203460129573, 360582203349225653, 360582203370077623, 360582203371150980, 360582203262553508, 360582203048652529, 360582202918335550, 360582202787673154, 360582202656797770]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592178780235697, 360592221885999614⟩, ⟨(-816934946850119674), (-814568131295219338)⟩, true⟩

def words09 : List Nat := [360582202625222534, 360582202476824944, 360582202329797592, 360582202439515957, 360582202484496361, 360582202529665408, 360582202530713086, 360582202500170362, 360582202596462536, 360582202721028763]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk812B

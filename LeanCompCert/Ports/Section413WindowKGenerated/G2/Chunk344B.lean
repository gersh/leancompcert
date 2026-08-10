import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk344A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk344B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk344A

def state06 : KState := ⟨⟨360636938057006649, 360636945282890507⟩, ⟨(-1908217363274313791), (-1908049013074452243)⟩, true⟩

def words05 : List Nat := [360581570413034047, 360581570248122531, 360581570547523531, 360581571332717689, 360581571400755878, 360581571468826513, 360581572377908516, 360581573709646189, 360581575316856498, 360581576924076937]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590636659283169, 360590643889570401⟩, ⟨(-312837748161021934), (-312669246198895698)⟩, true⟩

def words06 : List Nat := [360581577862431961, 360581577961865725, 360581577962243198, 360581577774652083, 360581577586949889, 360581577060046493, 360581576183756052, 360581574884001063, 360581573584225234, 360581573388389731]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550497977426247, 360550505212059409⟩, ⟨1071145271983045712, 1071313923771208458⟩, true⟩

def words07 : List Nat := [360581574492406424, 360581575596447787, 360581576277021092, 360581576837917942, 360581576838311402, 360581576820654129, 360581577171105398, 360581577171567142, 360581576702163445, 360581575801495929]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588233819068042, 360588241058065183⟩, ⟨(-230052974126244719), (-229884171846604809)⟩, true⟩

def words08 : List Nat := [360581574900776742, 360581574186674136, 360581574915954231, 360581575700774375, 360581575701203659, 360581575696870118, 360581575513749611, 360581575842387326, 360581575842768964, 360581576010028113]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586403545116789, 360586410788508432⟩, ⟨(-166974180744992877), (-166805226876605241)⟩, true⟩

def words09 : List Nat := [360581576010439444, 360581575781302976, 360581575598339404, 360581576066442750, 360581576321726243, 360581576577081576, 360581576577496763, 360581576412373459, 360581575853868351, 360581575994535023]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk344B

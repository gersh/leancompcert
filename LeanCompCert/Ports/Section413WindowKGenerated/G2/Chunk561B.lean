import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk561A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk561B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk561A

def state06 : KState := ⟨⟨360598492851687915, 360598512825364845⟩, ⟨(-938937504626053979), (-938179632640555975)⟩, true⟩

def words05 : List Nat := [360581804777480860, 360581804898129961, 360581805272576988, 360581805896315446, 360581806313265368, 360581806730323642, 360581806988574315, 360581807048570877, 360581807346670705, 360581807645032577]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591942848689017, 360591962829739566⟩, ⟨(-571208384289068464), (-570450098165471496)⟩, true⟩

def words06 : List Nat := [360581807869508619, 360581807870290610, 360581807778529765, 360581807492620663, 360581807206592843, 360581806787284234, 360581806846442310, 360581807034742627, 360581807050076804, 360581807231687805]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602562637907794, 360602582626337323⟩, ⟨(-1167830021255117575), (-1167071320617626981)⟩, true⟩

def words07 : List Nat := [360581807729568855, 360581808227662221, 360581808686135224, 360581808828564593, 360581808829299289, 360581808675247790, 360581808521056315, 360581808468704630, 360581808839115635, 360581809209690813]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584535815145202, 360584555811034716⟩, ⟨(-155046217665224959), (-154287097888168303)⟩, true⟩

def words08 : List Nat := [360581809389601062, 360581809578194467, 360581809906585831, 360581810235193562, 360581810380579688, 360581810434263042, 360581810434967212, 360581810327533816, 360581810219961201, 360581810049295503]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552167704413474, 360552187707669442⟩, ⟨1663976917254703540, 1664736450990098330⟩, true⟩

def words09 : List Nat := [360581810344857315, 360581810640558366, 360581810777598471, 360581810778380962, 360581810599429499, 360581810340334854, 360581810137206022, 360581810137988555, 360581809878978788, 360581809352704854]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk561B

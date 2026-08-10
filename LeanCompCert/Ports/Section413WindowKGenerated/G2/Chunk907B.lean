import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk907A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk907B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk907A

def state06 : KState := ⟨⟨360567771701127686, 360567825882062177⟩, ⟨1284159625468197943, 1287480270215037837⟩, true⟩

def words05 : List Nat := [360582011753373319, 360582011913873462, 360582011997248570, 360582011998559095, 360582011960635254, 360582011839224235, 360582011717417709, 360582011678597105, 360582011584274334, 360582011429332066]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574004795190881, 360574058988516476⟩, ⟨718385506271448116, 721707275695606522⟩, true⟩

def words06 : List Nat := [360582011274103638, 360582011092598034, 360582011004288773, 360582010903203544, 360582010802030005, 360582010597167724, 360582010356873398, 360582010216804520, 360582010076370819, 360582009933494945]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565670011072166, 360565724216880860⟩, ⟨1475001296250269112, 1478324198825793046⟩, true⟩

def words07 : List Nat := [360582009847069415, 360582009692482921, 360582009537640075, 360582009461106553, 360582009459143265, 360582009426459083, 360582009393609750, 360582009300124805, 360582009085216933, 360582008907328380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569053357834059, 360569107575998425⟩, ⟨1167789058560305374, 1171113082846193462⟩, true⟩

def words08 : List Nat := [360582008729005211, 360582008608401844, 360582008434477218, 360582008147405709, 360582007860126798, 360582007524480564, 360582007249388596, 360582007095719843, 360582006941911772, 360582006717785475]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580489959083958, 360580544189622175⟩, ⟨129442100106701484, 132767247875750668⟩, true⟩

def words09 : List Nat := [360582006576770149, 360582006531208714, 360582006559369337, 360582006616247865, 360582006617457102, 360582006571072224, 360582006524458862, 360582006422465195, 360582006398726627, 360582006383982041]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk907B

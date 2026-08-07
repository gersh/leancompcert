import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk561

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590661321626710, 360590681250936512⟩, ⟨(-499128513909934904), (-498373132252242670)⟩, true⟩

def state01 : KState := ⟨⟨360582448052262314, 360582467988920020⟩, ⟨(-38342872410023737), (-37587078497498667)⟩, true⟩

def words00 : List Nat := [360581798228944992, 360581798388412250, 360581798389108207, 360581798389546022, 360581798389868043, 360581798160476309, 360581798159124967, 360581798228945094, 360581798229641246, 360581798118867847]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584619373250010, 360584639317289004⟩, ⟨(-160198027394261918), (-159441819281172792)⟩, true⟩

def words01 : List Nat := [360581798179766974, 360581798240903660, 360581798618875261, 360581798680208603, 360581798680936664, 360581798458852063, 360581798236627573, 360581798177910050, 360581798229178931, 360581798280613229]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599224582999805, 360599244534478570⟩, ⟨(-980013683920144601), (-979257058249955223)⟩, true⟩

def words02 : List Nat := [360581798281312695, 360581798128526496, 360581798045982791, 360581798163746672, 360581798194409488, 360581798339623104, 360581798340319507, 360581798300313768, 360581798300588166, 360581798612292079]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584506139683218, 360584526098531388⟩, ⟨(-153689149456497018), (-152932110104987490)⟩, true⟩

def words03 : List Nat := [360581799240621578, 360581799869078331, 360581800201880582, 360581800614341648, 360581800904765668, 360581801195386347, 360581801720040205, 360581801928250486, 360581801977471397, 360581802026817223]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601205018260328, 360601224984484779⟩, ⟨(-1091228267461042151), (-1090470813968255655)⟩, true⟩

def words04 : List Nat := [360581802267436224, 360581802668677304, 360581803219115476, 360581803769688764, 360581804064088886, 360581804146692823, 360581804147338993, 360581804096439254, 360581804310229101, 360581804656904358]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk561

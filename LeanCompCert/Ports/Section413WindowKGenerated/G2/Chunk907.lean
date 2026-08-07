import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk907

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360547626011616790, 360547680118169101⟩, ⟨3110892860784399717, 3114206756838352455⟩, true⟩

def state01 : KState := ⟨⟨360589799191396912, 360589853310309335⟩, ⟨(-714465305129926040), (-711150287951969212)⟩, true⟩

def words00 : List Nat := [360582014986068196, 360582014645575142, 360582014365678712, 360582014207450031, 360582014049123070, 360582013787520400, 360582013617774551, 360582013534183377, 360582013486574418, 360582013574357224]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580708661765487, 360580762793186279⟩, ⟨110171056433100716, 113487208306593426⟩, true⟩

def words01 : List Nat := [360582013601297453, 360582013628375735, 360582013652471429, 360582013753578929, 360582013823853703, 360582013894340769, 360582013895515650, 360582013874453198, 360582013766730269, 360582013754477137]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565580543807683, 360565634687558568⟩, ⟨1482671525328151001, 1485988795850838163⟩, true⟩

def words02 : List Nat := [360582013827926653, 360582013829236681, 360582013795251962, 360582013700523188, 360582013605585678, 360582013449842285, 360582013354760082, 360582013208821474, 360582013062748399, 360582012829252064]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585301574238838, 360585355730352916⟩, ⟨(-306689229153386213), (-303370836856489495)⟩, true⟩

def words03 : List Nat := [360582012649797814, 360582012592064594, 360582012546919593, 360582012564144020, 360582012565354102, 360582012468055953, 360582012370509178, 360582012393339008, 360582012431250727, 360582012469458101]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587650393003649, 360587704561614326⟩, ⟨(-519962110046303535), (-516642583749445783)⟩, true⟩

def words04 : List Nat := [360582012470646938, 360582012401902985, 360582012252477156, 360582012196788217, 360582012140749761, 360582012054514037, 360582011939387118, 360582011762658788, 360582011585659916, 360582011593120872]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk907

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk151

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360439911815734197, 360439913105619458⟩, ⟨2125826166641072299, 2125839354882652991⟩, true⟩

def state01 : KState := ⟨⟨360641089174493637, 360641090466163349⟩, ⟨(-912957486131677628), (-912944270935983488)⟩, true⟩

def words00 : List Nat := [360580687846179292, 360580682887383498, 360580680168286635, 360580678050347017, 360580675932673417, 360580670176296954, 360580667098295821, 360580667739006348, 360580670593635707, 360580674592234689]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360520179620328926, 360520180913805221⟩, ⟨914591539031293389, 914604781533308743⟩, true⟩

def words01 : List Nat := [360580675687761466, 360580676783162113, 360580676783318331, 360580678159177437, 360580679464721344, 360580680770123348, 360580680770292046, 360580679880096413, 360580674648720787, 360580670648033615]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360473971327164925, 360473972622422857⟩, ⟨1613398983668114042, 1613412253117548374⟩, true⟩

def words02 : List Nat := [360580666997768856, 360580666997958224, 360580663007919027, 360580656511805387, 360580650016520785, 360580640710215688, 360580633618022852, 360580626395230060, 360580619173372903, 360580609255147084]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360718483678668302, 360718484975714324⟩, ⟨(-2087448301808420258), (-2087435005296279100)⟩, true⟩

def words03 : List Nat := [360580602207740278, 360580599505457437, 360580596803475802, 360580597968045974, 360580597968220555, 360580595733133450, 360580595604686979, 360580600372333206, 360580609479792004, 360580618586090371]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614468324265719, 360614469623119107⟩, ⟨(-512786112053527381), (-512772788169116359)⟩, true⟩

def words04 : List Nat := [360580624219028766, 360580627179958348, 360580631942349944, 360580636704167470, 360580638953353194, 360580638953542818, 360580636875057869, 360580630882325144, 360580624890344310, 360580625468398685]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360535539023838349, 360535540324477004⟩, ⟨683460361093044990, 683473712033276982⟩, true⟩

def words05 : List Nat := [360580630843838069, 360580636218604092, 360580639407462971, 360580639407652652, 360580638272114806, 360580634081131066, 360580629890643560, 360580627663852801, 360580627316300840, 360580624342421152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611228820486214, 360611230122918458⟩, ⟨(-463943178686846971), (-463929800546864101)⟩, true⟩

def words06 : List Nat := [360580622723845675, 360580627556829093, 360580635043284251, 360580642528788694, 360580646227419398, 360580646227609241, 360580647198693431, 360580648790890537, 360580648791047904, 360580650082014967]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360589993510619177, 360589994814859993⟩, ⟨(-141592424361519979), (-141579018776542007)⟩, true⟩

def words07 : List Nat := [360580650082184982, 360580649337105442, 360580652168731406, 360580657948577483, 360580662510098100, 360580667071051559, 360580669452382982, 360580669452573002, 360580668133563252, 360580668748146566]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360547600576920373, 360547601882952841⟩, ⟨501532976110603094, 501546408901859078⟩, true⟩

def words08 : List Nat := [360580668748301213, 360580668312468469, 360580663563348563, 360580655407917281, 360580647253528368, 360580637996072943, 360580630938054921, 360580628194367578, 360580625451020886, 360580620079720574]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360610417465081291, 360610418772908941⟩, ⟨(-453188985172412418), (-453175525103352514)⟩, true⟩

def words09 : List Nat := [360580617906338833, 360580616327461282, 360580617480484275, 360580617628602479, 360580617628777796, 360580614067121497, 360580610505900931, 360580604978812593, 360580604593428372, 360580606554955955]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk151

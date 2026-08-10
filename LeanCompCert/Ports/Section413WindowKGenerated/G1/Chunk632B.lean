import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk632A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk632B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk632A

def state06 : KState := ⟨⟨362492818120509339, 362492877041553362⟩, ⟨(-474223655130422354), (-471706049868930324)⟩, true⟩

def words05 : List Nat := [371285419666900707, 371285419818291395, 371285420173136189, 371285420195643820, 371285420197306706, 371285420181655895, 371285420277256707, 371285420295554073, 371285420414912443, 371285420535177097]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485647860102513, 362485706800547591⟩, ⟨(-20668524759601063), (-18149692089040671)⟩, true⟩

def words06 : List Nat := [371285420602139161, 371285420604289141, 371285420384697081, 371285420354994418, 371285420367841347, 371285420370028207, 371285420207901581, 371285420045590462, 371285419937120047, 371285419944134874]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477287681811625, 362477346641662539⟩, ⟨508351650810711885, 510871711386416397⟩, true⟩

def words07 : List Nat := [371285420080288605, 371285420217339327, 371285420298538003, 371285420300693510, 371285420126327517, 371285420028132229, 371285420077846137, 371285420079997833, 371285419960679065, 371285419835584575]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478411218806141, 362478470197881597⟩, ⟨437317704467025822, 439838981671542528⟩, true⟩

def words08 : List Nat := [371285419831608817, 371285419844651871, 371285419981838989, 371285420119878036, 371285420218928248, 371285420221078340, 371285419987265948, 371285419857865776, 371285419776658836, 371285419778884466]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485773238694892, 362485832237343093⟩, ⟨(-28643897700705577), (-26121381639023311)⟩, true⟩

def words09 : List Nat := [371285419670692852, 371285419538120308, 371285419492419932, 371285419516860025, 371285419616214942, 371285419716425389, 371285419807553956, 371285419809704549, 371285419574643364, 371285419583804618]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk632B

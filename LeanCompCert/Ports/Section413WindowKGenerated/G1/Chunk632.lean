import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk632

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497935841668825, 362497994646638264⟩, ⟨(-797268679710759374), (-794758413854370220)⟩, true⟩

def state01 : KState := ⟨⟨362490560925983305, 362490619750345085⟩, ⟨(-331217285906194976), (-328705794355359858)⟩, true⟩

def words00 : List Nat := [371285419753966853, 371285419756114096, 371285419622114238, 371285419592771103, 371285419606558093, 371285419608736256, 371285419538524643, 371285419467190235, 371285419529621125, 371285419614382115]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471799638327519, 362471858481992221⟩, ⟨854870626465038799, 857383338252492545⟩, true⟩

def words01 : List Nat := [371285419948371776, 371285420283204990, 371285420614813605, 371285420616961118, 371285420668755991, 371285420725126733, 371285420806689144, 371285420808837072, 371285420594440655, 371285420382312571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482147517190308, 362482206380063771⟩, ⟨200673861245608261, 203187787510135013⟩, true⟩

def words02 : List Nat := [371285420181898648, 371285420184266340, 371285420144262697, 371285420205048813, 371285420229592909, 371285420231741099, 371285419947763039, 371285419844675528, 371285419849096013, 371285419851319665]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483737523849563, 362483796406354173⟩, ⟨100139981461360646, 102655149098422280⟩, true⟩

def words03 : List Nat := [371285419802132402, 371285419705800014, 371285419706079756, 371285419708471219, 371285419734410785, 371285419786924714, 371285419842360257, 371285419844546177, 371285419692285404, 371285419669306394]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483296559503534, 362483355461129910⟩, ⟨128037199381701392, 130553576377184072⟩, true⟩

def words04 : List Nat := [371285419869460371, 371285419871609088, 371285419793002933, 371285419716731759, 371285419639693228, 371285419563102438, 371285419437674614, 371285419501587744, 371285419547048652, 371285419549293977]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk632

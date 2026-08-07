import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk264

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470270396011856, 362470279950227310⟩, ⟨397017352318896599, 397187871687804605⟩, true⟩

def state01 : KState := ⟨⟨362463738501874253, 362463748063542628⟩, ⟨569491365522010571, 569662081686721129⟩, true⟩

def words00 : List Nat := [371285324707702270, 371285324708539568, 371285323399249373, 371285322098630241, 371285320797780679, 371285319930729221, 371285318375236845, 371285318252383862, 371285318129251403, 371285318002266094]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504335494880792, 362504345064121622⟩, ⟨(-502991201481561903), (-502820285290276989)⟩, true⟩

def words01 : List Nat := [371285317186145865, 371285316541196352, 371285316449286046, 371285316450123818, 371285315399751784, 371285314079581869, 371285312869289051, 371285312870230532, 371285313258295500, 371285313979556683]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468760462854355, 362468770039648992⟩, ⟨437084508675280655, 437255624477402789⟩, true⟩

def words02 : List Nat := [371285314696778057, 371285314697621596, 371285314999273779, 371285315865993234, 371285316754660371, 371285316755498523, 371285315985552910, 371285315096483371, 371285314207152918, 371285313952796075]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362431500603880785, 362431510188236848⟩, ⟨1422239881621169615, 1422411197310537281⟩, true⟩

def words03 : List Nat := [371285314131404341, 371285314936247734, 371285315455191257, 371285315456029611, 371285314069041699, 371285312794192531, 371285311672687272, 371285311673525762, 371285309922426112, 371285307888588987]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493761162191197, 362493770754061171⟩, ⟨(-224167421892139691), (-223995907497782523)⟩, true⟩

def words04 : List Nat := [371285305854526718, 371285305094359761, 371285303850548839, 371285303783063987, 371285303715326221, 371285303325547651, 371285301749640077, 371285301390564575, 371285302098843210, 371285302419877293]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474965040645091, 362474974640164821⟩, ⟨273097548612080959, 273269265380432451⟩, true⟩

def words05 : List Nat := [371285302749839824, 371285303080048569, 371285304002882307, 371285304215485214, 371285304305527041, 371285304395882670, 371285304481696856, 371285304482535951, 371285302666069621, 371285302276800514]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362438107999626922, 362438117606619485⟩, ⟨1248637440833438842, 1248809355371791986⟩, true⟩

def words06 : List Nat := [371285302658844191, 371285302659683449, 371285301726510649, 371285300789781798, 371285299852792049, 371285299240697539, 371285298137460836, 371285297455920361, 371285296774160087, 371285295897339991]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495585351598233, 362495594966184699⟩, ⟨(-273032951494067146), (-272860835906214718)⟩, true⟩

def words07 : List Nat := [371285294115647050, 371285293555556364, 371285293449491461, 371285293450346329, 371285292973747227, 371285292246500327, 371285291518980049, 371285291198621379, 371285290552998918, 371285290943077331]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481785323518521, 362481794945692453⟩, ⟨92262707428307038, 92435023971164658⟩, true⟩

def words08 : List Nat := [371285291001297315, 371285291002137255, 371285289161493975, 371285288533577116, 371285287905303246, 371285287709472835, 371285286515429699, 371285285328151408, 371285284375613329, 371285284376570942]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362459829758850080, 362459839388583166⟩, ⟨674161120490666288, 674333637313019422⟩, true⟩

def words09 : List Nat := [371285285273244067, 371285286301894338, 371285287327746275, 371285287328590667, 371285287003144748, 371285286740683273, 371285287636557923, 371285287637398490, 371285286900281293, 371285285940934601]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk264

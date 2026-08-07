import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk004

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨355026784850885841, 355026784851464029⟩, ⟨2089435310107011003, 2089435310265917909⟩, true⟩

def state01 : KState := ⟨⟨360614267015914682, 360614267016524542⟩, ⟨(-174316403956893843), (-174316403785156633)⟩, true⟩

def words00 : List Nat := [360237346722454068, 360230196827786910, 360226734806727077, 360223485605562581, 360220252449835699, 360211867658003714, 360205297784528095, 360198010067242052, 360190757986714436, 360190139513397641]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361015933887388907, 361015933888031700⟩, ⟨(-353537858270233811), (-353537858084825453)⟩, true⟩

def words01 : List Nat := [360190139513400677, 360187967348568957, 360185805702694692, 360182868874254358, 360182868874257259, 360181375729778407, 360179889746663603, 360175417028559773, 360174177083063848, 360176176505407412]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨358366525175833898, 358366525176509970⟩, ⟨774711940700711069, 774711940900269339⟩, true⟩

def words02 : List Nat := [360183385961230199, 360185556505502154, 360185556505505314, 360184563354603699, 360183574877352841, 360179397156974145, 360178390786467883, 360176470093556603, 360174558354924308, 360168180853022225]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨364607417944135531, 364607417944846198⟩, ⟨(-1938996636040510804), (-1938996635825897716)⟩, true⟩

def words03 : List Nat := [360164839957791261, 360165675361561284, 360171485563344374, 360178397572028655, 360180672812329865, 360182937639632319, 360185367437692046, 360190569116078710, 360200607408874391, 360210600176533505]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨365347151297736815, 365347151298483337⟩, ⟨(-2283288028469424341), (-2283288028238855103)⟩, true⟩

def words04 : List Nat := [360216603842802512, 360223339459959976, 360234840770269112, 360246290389297011, 360255924529544836, 360261172232434622, 360263632946638528, 360266082699977870, 360273177902392686, 360284428397731996]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨358766482872095702, 358766482872878687⟩, ⟨713248876879085000, 713248877126253024⟩, true⟩

def words05 : List Nat := [360295044538058424, 360305613808008838, 360313507619545152, 360317131974175233, 360317131974178548, 360316754749121608, 360320500922321895, 360320500922325805, 360320401995154073, 360317023910109672]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨363627705864421308, 363627705865241881⟩, ⟨(-1533424500610745271), (-1533424500346095973)⟩, true⟩

def words06 : List Nat := [360314750152325984, 360320189065018809, 360330024958074762, 360339818546215094, 360345758044356722, 360347548722024260, 360353708416479601, 360359841843582347, 360365100545352413, 360372027520558026]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361405130665371764, 361405130666231123⟩, ⟨(-481573073664829374), (-481573073381750642)⟩, true⟩

def words07 : List Nat := [360376448089692814, 360380849967203825, 360384853117614039, 360391261757036396, 360395612878111710, 360399945755493507, 360401805663329996, 360401805663334089, 360401853430014539, 360403939245479043]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360279041102176640, 360279041103075406⟩, ⟨48222307472644136, 48222307774839024⟩, true⟩

def words08 : List Nat := [360406002632936692, 360406002632940817, 360404187322240177, 360398876936584594, 360393588449425906, 360386701584971680, 360381955542514798, 360381225534380446, 360380498511964010, 360377453976085282]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨363010777886803560, 363010777887742612⟩, ⟨(-1306169030814383078), (-1306169030492241944)⟩, true⟩

def words09 : List Nat := [360380990053014661, 360384711405237592, 360388400386919730, 360392433639383021, 360392441827926911, 360392449983519215, 360392449983522766, 360393204680335381, 360398439826753699, 360403654074384844]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk004

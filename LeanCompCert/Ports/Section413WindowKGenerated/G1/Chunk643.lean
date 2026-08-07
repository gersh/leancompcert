import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk643

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476155306671527, 362476216259015651⟩, ⟨594743052861456742, 597390217655647250⟩, true⟩

def state01 : KState := ⟨⟨362499360354191442, 362499421326122760⟩, ⟨(-897381812731119755), (-894733388379327545)⟩, true⟩

def words00 : List Nat := [371285506885607459, 371285506897204271, 371285507149774978, 371285507403255802, 371285507613957551, 371285507651739312, 371285507902442104, 371285508154250014, 371285508504881758, 371285508723482787]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499061031269605, 362499122023157319⟩, ⟨(-878115154322403223), (-875465446476433233)⟩, true⟩

def words01 : List Nat := [371285508906046946, 371285509089350619, 371285509487102975, 371285509768057238, 371285510108390423, 371285510449568239, 371285510743166346, 371285510745353892, 371285510928273771, 371285511142628776]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362497680194462547, 362497741205862254⟩, ⟨(-789279519706958905), (-786628556749382857)⟩, true⟩

def words02 : List Nat := [371285511575693104, 371285511748492831, 371285511872149794, 371285511996488410, 371285512181296913, 371285512256173140, 371285512571861948, 371285512888473764, 371285513183089421, 371285513375473338]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508981203166119, 362509042234306667⟩, ⟨(-1516285188638116120), (-1513632955648675816)⟩, true⟩

def words03 : List Nat := [371285513741707623, 371285514109062324, 371285514716970411, 371285515076607580, 371285515398518472, 371285515721128980, 371285516084912321, 371285516329200400, 371285516696344859, 371285517064420457]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493435685231148, 362493496736140992⟩, ⟨(-516071889703315272), (-513418384659880142)⟩, true⟩

def words04 : List Nat := [371285517431744744, 371285517514973323, 371285517755092912, 371285517996402768, 371285518256921249, 371285518259109711, 371285518197859050, 371285518129136737, 371285518203913419, 371285518330449397]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484997422839200, 362485058493476682⟩, ⟨26978458765426834, 29633233384593504⟩, true⟩

def words05 : List Nat := [371285518513060956, 371285518696560424, 371285518875853504, 371285518878045372, 371285518796274248, 371285518767894383, 371285518931191261, 371285518933418357, 371285518927508514, 371285518922833186]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490607734748018, 362490668824975647⟩, ⟨(-334113901634984188), (-331457866095077602)⟩, true⟩

def words06 : List Nat := [371285519033777710, 371285519054506660, 371285519232847458, 371285519412046043, 371285519528580844, 371285519530770146, 371285519336967615, 371285519351198446, 371285519562710030, 371285519644970753]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482496282379266, 362482557392559772⟩, ⟨188135721118348956, 190793041123532164⟩, true⟩

def words07 : List Nat := [371285519720100247, 371285519796008260, 371285520112376785, 371285520309452063, 371285520566429968, 371285520824266998, 371285521062436094, 371285521064625743, 371285520981119388, 371285520937777597]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475664984179964, 362475726113866924⟩, ⟨627986447953903388, 630645023884676528⟩, true⟩

def words08 : List Nat := [371285521088550233, 371285521090740162, 371285520966202609, 371285520795898594, 371285520624730277, 371285520512361809, 371285520319312326, 371285520302499671, 371285520284976305, 371285520259291442]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498273862165988, 362498335011701591⟩, ⟨(-827935205908632769), (-825275351825568761)⟩, true⟩

def words09 : List Nat := [371285520132019177, 371285520158001298, 371285520282537384, 371285520284742451, 371285520193174471, 371285520064991257, 371285520013835586, 371285520016249143, 371285520174506087, 371285520376030941]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk643

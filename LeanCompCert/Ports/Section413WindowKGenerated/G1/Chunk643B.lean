import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk643A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk643B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk643A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk643B

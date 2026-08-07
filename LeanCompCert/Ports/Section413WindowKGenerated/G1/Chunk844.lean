import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk844

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471879446492822, 362471986703062907⟩, ⟨1119136324939608749, 1125248726393854035⟩, true⟩

def state01 : KState := ⟨⟨362482580199145769, 362482687481930147⟩, ⟨215971638648348707, 222086252726081305⟩, true⟩

def words00 : List Nat := [371285318877967209, 371285318863585967, 371285318778185780, 371285318765978311, 371285318752891439, 371285318702278368, 371285318534233485, 371285318508035388, 371285318520862526, 371285318523900602]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475492627748763, 362475599937266816⟩, ⟨814298407631301168, 820415278430203274⟩, true⟩

def words01 : List Nat := [371285318494942542, 371285318469886303, 371285318463657944, 371285318466909387, 371285318452889198, 371285318469486939, 371285318479865714, 371285318482796482, 371285318305957165, 371285318194533225]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469565393532493, 362469672729121186⟩, ⟨1314762406647524171, 1320881478467195863⟩, true⟩

def words02 : List Nat := [371285318106547050, 371285318109500122, 371285318038423648, 371285317963991979, 371285317888428837, 371285317819002771, 371285317678316140, 371285317597403756, 371285317515553554, 371285317422695357]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493853816906254, 362493961179031322⟩, ⟨(-736012714746776504), (-729891402325990704)⟩, true⟩

def words03 : List Nat := [371285317239387594, 371285317197874986, 371285317210037694, 371285317213021763, 371285317171578419, 371285317118551623, 371285317148330592, 371285317165589069, 371285317269951290, 371285317375638113]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481865131708016, 362481972520314344⟩, ⟨276325411167445735, 282448959799060581⟩, true⟩

def words04 : List Nat := [371285317453440096, 371285317456371759, 371285317375865214, 371285317408191731, 371285317481914905, 371285317484846735, 371285317371841244, 371285317231785289, 371285317090422934, 371285317090590236]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477706874226679, 362477814289188716⟩, ⟨627546346929102067, 633672121428960227⟩, true⟩

def words05 : List Nat := [371285317140360312, 371285317230900057, 371285317320412636, 371285317323344604, 371285317225904202, 371285317132217286, 371285317079797806, 371285317082749984, 371285317004652842, 371285316919089604]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480819826887827, 362480927268108499⟩, ⟨364666853152349348, 370794845594581958⟩, true⟩

def words06 : List Nat := [371285316832258558, 371285316820552864, 371285316830055062, 371285316907091758, 371285316961269728, 371285316964202301, 371285316865577975, 371285316888806160, 371285316928214369, 371285316931250379]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478673992857124, 362478781460857073⟩, ⟨545956644251305944, 552086898865248252⟩, true⟩

def words07 : List Nat := [371285316881477058, 371285316820117405, 371285316781322227, 371285316784607145, 371285316791404858, 371285316815392167, 371285316826739309, 371285316829672116, 371285316654052665, 371285316580398566]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472192269407547, 362472299763532259⟩, ⟨1093576149436374327, 1099708611207156209⟩, true⟩

def words08 : List Nat := [371285316567746850, 371285316570680489, 371285316469696802, 371285316336406836, 371285316202023329, 371285316101945858, 371285315930693506, 371285315823185133, 371285315714661696, 371285315606959969]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481573126303900, 362481680646898644⟩, ⟨300926515426986361, 307061213786372291⟩, true⟩

def words09 : List Nat := [371285315454912828, 371285315376283966, 371285315317206355, 371285315320140143, 371285315174583494, 371285315006899536, 371285314838021694, 371285314728167594, 371285314547133459, 371285314507416826]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk844

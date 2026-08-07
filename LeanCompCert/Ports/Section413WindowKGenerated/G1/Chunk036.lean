import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk036

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362421325154250898, 362421325302036828⟩, ⟨180622869715502447, 180623230661246645⟩, true⟩

def state01 : KState := ⟨⟨362232772935727747, 362232773084369176⟩, ⟨860250573218610840, 860250937248671280⟩, true⟩

def words00 : List Nat := [371271520000646123, 371271520000742088, 371271453502087162, 371271387062918903, 371271320660575731, 371271255214620384, 371271151842037155, 371271124807960908, 371271097788833423, 371271069742886814]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362559476113162542, 362559476262675380⟩, ⟨(-320004595595251208), (-320004228414935758)⟩, true⟩

def words01 : List Nat := [371271003751078163, 371270988485099408, 371271034008435521, 371271034008532286, 371271024503231658, 371271002313140434, 371271033926248764, 371271052878025944, 371271077304442621, 371271101717407516]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362437574129268673, 362437574279652823⟩, ⟨120798992298496707, 120799362637485353⟩, true⟩

def words02 : List Nat := [371271115217300915, 371271115217397501, 371271027725705828, 371271016064146668, 371271007478926238, 371271007479024524, 371270954333268235, 371270902462569555, 371270852340874974, 371270852340985464]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471137900915481, 362471138052173042⟩, ⟨(-239959262218523), (-239585748266513)⟩, true⟩

def words03 : List Nat := [371270909466760094, 371270975721066189, 371271026906555401, 371271026906652282, 371271002567539476, 371271000534334813, 371271071733428018, 371271072213640819, 371271072231800990, 371271072249990053]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471541734104700, 362471541886230176⟩, ⟨(-856577574452066), (-856200896822012)⟩, true⟩

def words04 : List Nat := [371271108287515663, 371271108287622226, 371271181339208248, 371271255341560736, 371271317359416214, 371271317359513248, 371271279650312045, 371271271976352837, 371271307310541545, 371271307374891688]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362542726802008567, 362542726955019024⟩, ⟨(-260959821083842619), (-260959441171514357)⟩, true⟩

def words05 : List Nat := [371271307374964554, 371271307096197157, 371271354643630113, 371271380592280995, 371271409821892711, 371271439035556188, 371271461953463397, 371271461953560797, 371271426561137424, 371271446036916999]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362237959756518619, 362237959910399918⟩, ⟨855774385811136960, 855774768915315734⟩, true⟩

def words06 : List Nat := [371271495555798400, 371271495555895897, 371271446275719273, 371271377625685513, 371271309013076283, 371271262559572557, 371271192261016806, 371271175238010751, 371271158224250732, 371271141046344146]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362794002292673804, 362794002447441446⟩, ⟨(-1187136092142385128), (-1187135705780881842)⟩, true⟩

def words07 : List Nat := [371271087771373803, 371271098010663482, 371271181934355442, 371271202776443933, 371271205286970898, 371271207796160274, 371271283898443622, 371271323538379968, 371271411222933270, 371271498859888911]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468257132889672, 362468257288544600⟩, ⟨13352646364548819, 13353035995877041⟩, true⟩

def words08 : List Nat := [371271585663390985, 371271612731485016, 371271689801653659, 371271766830042092, 371271844206307489, 371271849671958980, 371271854786162526, 371271859897626972, 371271875997373782, 371271875997486573]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362402608679120805, 362402608835662057⟩, ⟨257084026223704379, 257084419130065231⟩, true⟩

def words09 : List Nat := [371271947139390127, 371272019222688059, 371272090936555125, 371272090936653602, 371272065552465381, 371272061802654713, 371272127124636305, 371272127124734865, 371272109895063221, 371272091111102616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk036

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk773

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614081554730771, 360614120369729943⟩, ⟨(-2471897070557929196), (-2469870589156265868)⟩, true⟩

def state01 : KState := ⟨⟨360594176073799115, 360594214899321404⟩, ⟨(-933237368281453639), (-931210073391030193)⟩, true⟩

def words00 : List Nat := [360582169312496184, 360582169429190529, 360582169623565269, 360582169818257441, 360582169970828966, 360582169971932032, 360582169957688622, 360582169849842375, 360582169754170992, 360582169911242205]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570295552307131, 360570334388214457⟩, ⟨913107064726284819, 915135162535745903⟩, true⟩

def words01 : List Nat := [360582170044368109, 360582170177695680, 360582170227330956, 360582170280399666, 360582170281339412, 360582170212631259, 360582170240648869, 360582170241752269, 360582170225126930, 360582170073192933]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611052778904487, 360611091625246739⟩, ⟨(-2238420088625434017), (-2236391183938305825)⟩, true⟩

def words02 : List Nat := [360582169921012867, 360582170021158738, 360582170303839147, 360582170586728783, 360582170727597372, 360582170841958207, 360582171071178727, 360582171300729413, 360582171526021453, 360582171901152414]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603283139402680, 360603321996239573⟩, ⟨(-1637567299107449202), (-1635537582815497234)⟩, true⟩

def words03 : List Nat := [360582172179828447, 360582172458617530, 360582172794100266, 360582173213655611, 360582173591156180, 360582173968846146, 360582174243147204, 360582174350819306, 360582174625148776, 360582174899837723]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593959981667623, 360593998848919280⟩, ⟨(-916590842768428954), (-914560320949187964)⟩, true⟩

def words04 : List Nat := [360582175152604372, 360582175238850052, 360582175239851396, 360582175181623524, 360582175123217985, 360582174995260055, 360582175071157164, 360582175193183841, 360582175194171040, 360582175338932995]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360608669490806052, 360608708368463573⟩, ⟨(-2054450972414986244), (-2052419645650290948)⟩, true⟩

def words05 : List Nat := [360582175659508792, 360582175980408418, 360582176429358412, 360582176711831582, 360582176851914785, 360582176992069586, 360582177085421174, 360582177262799219, 360582177606648078, 360582177950738230]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588463440389095, 360588502328560766⟩, ⟨(-491348504949459823), (-489316364758625615)⟩, true⟩

def words06 : List Nat := [360582178201996356, 360582178342800427, 360582178426219910, 360582178509983596, 360582178551683315, 360582178552787375, 360582178474335689, 360582178247450540, 360582178020357529, 360582178042138740]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582863416554574, 360582902315138181⟩, ⟨(-58065191058548968), (-56032245243419992)⟩, true⟩

def words07 : List Nat := [360582178119052975, 360582178196163366, 360582178197156433, 360582178189789816, 360582178157545933, 360582178080576379, 360582178091819875, 360582178185725155, 360582178196067103, 360582178206568333]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600468466707970, 360600507375714248⟩, ⟨(-1420386996638441622), (-1418353244265263188)⟩, true⟩

def words08 : List Nat := [360582178346461140, 360582178573387706, 360582178966673542, 360582179360163656, 360582179572857786, 360582179619093536, 360582179739049179, 360582179859323877, 360582180029380605, 360582180267339046]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584721002389789, 360584759921932498⟩, ⟨(-201558277963876908), (-199523710124129282)⟩, true⟩

def words09 : List Nat := [360582180420736144, 360582180574259594, 360582180865837400, 360582181241357860, 360582181529414678, 360582181817650244, 360582182022369413, 360582182060732219, 360582182094946611, 360582182129525112]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk773

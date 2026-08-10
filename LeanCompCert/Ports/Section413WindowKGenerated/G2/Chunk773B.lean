import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk773A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk773B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk773A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk773B

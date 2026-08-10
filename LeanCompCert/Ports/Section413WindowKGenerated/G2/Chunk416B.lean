import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk416A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk416B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk416A

def state06 : KState := ⟨⟨360624857143502942, 360624867869357332⟩, ⟨(-1769314231369675176), (-1769012243884343292)⟩, true⟩

def words05 : List Nat := [360582399246259883, 360582400238714153, 360582401498849900, 360582402397425862, 360582402807600014, 360582403217798855, 360582403316058470, 360582403761064147, 360582404780823858, 360582405800662766]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611145706020184, 360611156437275040⟩, ⟨(-1198222767645446093), (-1197920555150321023)⟩, true⟩

def words06 : List Nat := [360582406527492908, 360582406942395811, 360582407761733166, 360582408581208166, 360582409083110843, 360582409175684218, 360582409176191615, 360582408807155490, 360582408643123089, 360582409333650210]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583232798304125, 360583243534900881⟩, ⟨(-34992447080958186), (-34690011962164832)⟩, true⟩

def words07 : List Nat := [360582410010613101, 360582410687643981, 360582411014355452, 360582411014922197, 360582410960290210, 360582410760669419, 360582410756802874, 360582411219879163, 360582411240361345, 360582411260916040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360659546852228516, 360659557594172748⟩, ⟨(-3216160664531131675), (-3215858006502633037)⟩, true⟩

def words08 : List Nat := [360582411855676114, 360582412737868458, 360582414033985358, 360582415330149961, 360582416081513055, 360582416583498192, 360582417659504247, 360582418735631032, 360582420198367395, 360582422049174964]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614163712422191, 360614174459767779⟩, ⟨(-1323772880863829251), (-1323469997626124205)⟩, true⟩

def words09 : List Nat := [360582423538724629, 360582425028272038, 360582426968555740, 360582429195868616, 360582431169267358, 360582433142663509, 360582434761229006, 360582435807903020, 360582436569489288, 360582437331218677]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk416B

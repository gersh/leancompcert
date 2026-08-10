import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk879A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603940797913301, 360603991492143377⟩, ⟨(-1921628432050918864), (-1918619283138432810)⟩, true⟩

def state01 : KState := ⟨⟨360595968477980714, 360596019184130808⟩, ⟨(-1220896543217343069), (-1217886346477159795)⟩, true⟩

def words00 : List Nat := [360582164677252490, 360582164780629746, 360582164819238858, 360582164857975441, 360582164864040051, 360582164980719710, 360582165140823497, 360582165301163583, 360582165396601296, 360582165555500977]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605332864077347, 360605383582195759⟩, ⟨(-2044192149605669631), (-2041180900671225257)⟩, true⟩

def words01 : List Nat := [360582165843339445, 360582166131568001, 360582166377014681, 360582166519383020, 360582166551755923, 360582166584227597, 360582166745674435, 360582166972494394, 360582167237587858, 360582167502980655]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581838671348709, 360581889401527301⟩, ⟨21439638823468853, 24451948149055763⟩, true⟩

def words02 : List Nat := [360582167703585952, 360582167775128523, 360582167866463606, 360582167958165457, 360582168015956109, 360582168017222318, 360582167945919062, 360582167772163663, 360582167598169843, 360582167485777831]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579331150557553, 360579381892657486⟩, ⟨242019237674324140, 245032595304031466⟩, true⟩

def words03 : List Nat := [360582167609647676, 360582167736928843, 360582167799334885, 360582167930920495, 360582168006965380, 360582168083344118, 360582168247627137, 360582168282993626, 360582168284133495, 360582168253759420]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585107956136192, 360585158710211136⟩, ⟨(-266046006128580646), (-263031595357936872)⟩, true⟩

def words04 : List Nat := [360582168223119396, 360582168137533313, 360582168223651319, 360582168332032137, 360582168333214296, 360582168310489920, 360582168158390812, 360582168085841281, 360582168014238086, 360582168049555113]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk879A

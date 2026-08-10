import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk569A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505017236968598, 362505064507375741⟩, ⟨(-1147269796118294099), (-1145452864583617045)⟩, true⟩

def state01 : KState := ⟨⟨362485474061064053, 362485521348782614⟩, ⟨(-35253029015064245), (-33435112370692295)⟩, true⟩

def words00 : List Nat := [371284934230166701, 371284934248240745, 371284934300525925, 371284934353787717, 371284934472180184, 371284934474098927, 371284934237036930, 371284934001990257, 371284933837993409, 371284933850542016]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480870169549647, 362480917474552941⟩, ⟨226888145125478481, 228707045530714041⟩, true⟩

def words01 : List Nat := [371284934171058383, 371284934492368271, 371284934796239747, 371284934916182576, 371284935128795523, 371284935342359216, 371284935652762665, 371284935654681150, 371284935586640449, 371284935518220031]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492287826305342, 362492335148483619⟩, ⟨(-422986599935901672), (-421166721843891524)⟩, true⟩

def words02 : List Nat := [371284935687139971, 371284935791391759, 371284936203606445, 371284936616609726, 371284936916582746, 371284936918501462, 371284936824327882, 371284936844015316, 371284937171408112, 371284937303340483]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495263143671754, 362495310483332428⟩, ⟨(-592403580687019705), (-590582707235093837)⟩, true⟩

def words03 : List Nat := [371284937376033542, 371284937449329778, 371284937715815009, 371284937828708656, 371284938000924420, 371284938173899340, 371284938345075185, 371284938347028344, 371284938462925645, 371284938647445544]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480219949151553, 362480267305892252⟩, ⟨264271507003236669, 266093353080296379⟩, true⟩

def words04 : List Nat := [371284939139506309, 371284939264482561, 371284939353692281, 371284939443552661, 371284939551147672, 371284939553262633, 371284939579941732, 371284939654688629, 371284939706936575, 371284939708931415]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk569A

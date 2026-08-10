import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk196A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360513777420193581, 360513779646004587⟩, ⟨1366178116407276437, 1366207641817107569⟩, true⟩

def state01 : KState := ⟨⟨360603052539376910, 360603054767554838⟩, ⟨(-384066524540772362), (-384036952727827316)⟩, true⟩

def words00 : List Nat := [360583480561560167, 360583477854975103, 360583478966098482, 360583480816851645, 360583480817082750, 360583480453568954, 360583477497315219, 360583474480658821, 360583471464236402, 360583472035785534]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585280921785316, 360585283152353715⟩, ⟨(-35506292874807710), (-35476674172788780)⟩, true⟩

def words01 : List Nat := [360583472036011025, 360583471719610087, 360583471474130027, 360583473492297832, 360583474852904879, 360583476213414111, 360583476213638675, 360583475927366966, 360583474962759936, 360583475055204091]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360539366896816157, 360539369129751352⟩, ⟨865226309030167214, 865255974180690774⟩, true⟩

def words02 : List Nat := [360583475088956082, 360583475089207128, 360583472533667556, 360583468487221589, 360583464441145740, 360583459566481345, 360583456016187760, 360583453577481044, 360583451138993383, 360583447376016288]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582397471799070, 360582399707103804⟩, ⟨20200474918725769, 20230186595172669⟩, true⟩

def words03 : List Nat := [360583445130880723, 360583444650814425, 360583445068571535, 360583445068822726, 360583443380136396, 360583438777058777, 360583434174402086, 360583431342328510, 360583429809526910, 360583429757337775]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602831603722970, 360602833841424930⟩, ⟨(-381394620910264489), (-381364862140676349)⟩, true⟩

def words04 : List Nat := [360583429705117884, 360583428353278459, 360583428517773852, 360583428970501400, 360583428970711974, 360583429511844373, 360583429512070623, 360583428380839009, 360583427249678064, 360583426948028122]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk196A

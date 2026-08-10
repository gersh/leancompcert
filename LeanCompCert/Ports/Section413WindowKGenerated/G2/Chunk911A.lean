import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk911A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589944983147780, 360589999586657698⟩, ⟨(-733362064365033841), (-730002994825246093)⟩, true⟩

def state01 : KState := ⟨⟨360575906583584190, 360575961199623736⟩, ⟨545539712055221498, 548899923106051460⟩, true⟩

def words00 : List Nat := [360581986498158796, 360581986559655396, 360581986605724665, 360581986652182244, 360581986653305282, 360581986603393869, 360581986433062011, 360581986192291694, 360581985951275174, 360581985784445447]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547951540183239, 360548006168635631⟩, ⟨3092723174831765842, 3096084516879751586⟩, true⟩

def words01 : List Nat := [360581985753739355, 360581985789431360, 360581985790612004, 360581985731874742, 360581985552647272, 360581985343602312, 360581985134167198, 360581984919708224, 360581984640659516, 360581984269128166]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595874563377569, 360595929204255297⟩, ⟨(-1274283847508925164), (-1270921373203766816)⟩, true⟩

def words02 : List Nat := [360581983897302320, 360581983646146481, 360581983455056622, 360581983366300160, 360581983277445570, 360581983086379837, 360581982933981976, 360581982902233518, 360581982957157771, 360581983111562320]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578372754546873, 360578427407975842⟩, ⟨320719741937977099, 324083360098017565⟩, true⟩

def words03 : List Nat := [360581983186856084, 360581983262291345, 360581983311936592, 360581983434976275, 360581983479995740, 360581983525221766, 360581983526397932, 360581983488671391, 360581983330475180, 360581983292988987]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570138023327076, 360570192689150059⟩, ⟨1071285941033219371, 1074650688845842459⟩, true⟩

def words04 : List Nat := [360581983336262039, 360581983337578826, 360581983323550329, 360581983217021390, 360581983110279916, 360581982973719422, 360581982928878456, 360581982845778377, 360581982762538139, 360581982603454457]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk911A

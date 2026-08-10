import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk996A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589605272052234, 360589670993624273⟩, ⟨(-724682059910009876), (-720262132118013530)⟩, true⟩

def state01 : KState := ⟨⟨360590569111941188, 360590634847170451⟩, ⟨(-820745307650043937), (-816324019531223057)⟩, true⟩

def words00 : List Nat := [360582439669833462, 360582439720696553, 360582439722027336, 360582439684897524, 360582439647539489, 360582439545389528, 360582439568854661, 360582439631814926, 360582439644163724, 360582439727961416]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583077339386243, 360583143088284744⟩, ⟨(-74428431404673803), (-70005781625621223)⟩, true⟩

def words01 : List Nat := [360582439912125680, 360582440096726899, 360582440287779104, 360582440378590817, 360582440379927708, 360582440379725892, 360582440379259867, 360582440350366873, 360582440358597601, 360582440367155408]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576096700583593, 360576162463280114⟩, ⟨620934729087686024, 625358753492715964⟩, true⟩

def words02 : List Nat := [360582440368457862, 360582440326418780, 360582440183605352, 360582440141951909, 360582440099888591, 360582440030713318, 360582439880843623, 360582439654973239, 360582439428829714, 360582439275018474]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563358934791019, 360563424711151913⟩, ⟨1890030963348653185, 1894456349202532955⟩, true⟩

def words03 : List Nat := [360582439213209711, 360582439123847642, 360582439034322139, 360582438894525481, 360582438693660757, 360582438467717482, 360582438241350505, 360582438049812875, 360582437910799282, 360582437721481124]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577782528717963, 360577848318747989⟩, ⟨452822754924764925, 457249502839079909⟩, true⟩

def words04 : List Nat := [360582437531837573, 360582437401319623, 360582437339540509, 360582437359845697, 360582437361211862, 360582437291113617, 360582437120293617, 360582437033104187, 360582436945483714, 360582436873718778]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk996A

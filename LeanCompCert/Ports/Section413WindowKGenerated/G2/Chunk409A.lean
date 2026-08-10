import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk409A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565768183656783, 360565778506205505⟩, ⟨679837860292063451, 680123198837662287⟩, true⟩

def state01 : KState := ⟨⟨360586815893220268, 360586826221014700⟩, ⟨(-181069387217005212), (-180783834095564718)⟩, true⟩

def words00 : List Nat := [360582407029163870, 360582406608758953, 360582407201136136, 360582407795765556, 360582407856722970, 360582407857278263, 360582407464358318, 360582407332463717, 360582407200405521, 360582407266843559]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360551810849524561, 360551821182606415⟩, ⟨1251234859832763920, 1251520629288293918⟩, true⟩

def words01 : List Nat := [360582407267340629, 360582407000067204, 360582406912114530, 360582407394294068, 360582407451923317, 360582407509632282, 360582407510127801, 360582407174673570, 360582406500018576, 360582405753214634]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587618097942995, 360587628436259191⟩, ⟨(-214119220141740283), (-213833236470361081)⟩, true⟩

def words02 : List Nat := [360582405006258635, 360582404714982327, 360582404639274459, 360582404263751492, 360582403888154259, 360582403363197362, 360582403650910660, 360582404092862227, 360582404093365707, 360582404199458958]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608913274321107, 360608923617881422⟩, ⟨(-1085939232914541128), (-1085653034575317306)⟩, true⟩

def words03 : List Nat := [360582404305659612, 360582404412020924, 360582405113645470, 360582405416874914, 360582405417387191, 360582405215429799, 360582405013367051, 360582404819753606, 360582405467950881, 360582406116243082]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600128996396184, 360600139345262386⟩, ⟨(-726497388233873906), (-726210972646855226)⟩, true⟩

def words04 : List Nat := [360582406465187696, 360582406729262753, 360582406978876955, 360582407228633977, 360582407229100135, 360582407188476438, 360582406780783604, 360582406073999487, 360582405367143089, 360582405688632589]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk409A

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk593A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk593B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk593A

def state06 : KState := ⟨⟨360600079360856587, 360600101774733646⟩, ⟨(-1073000669722876880), (-1072101813267426986)⟩, true⟩

def words05 : List Nat := [360582041646067557, 360582041697135724, 360582041697818113, 360582041682043045, 360582041480512725, 360582041037111741, 360582040593559181, 360582040454547217, 360582040759485327, 360582041064616441]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360569442778119277, 360569465199892337⟩, ⟨745573199372390983, 746472524573203863⟩, true⟩

def words06 : List Nat := [360582041204543895, 360582041205373771, 360582041149612286, 360582041083829613, 360582041017818658, 360582040831548081, 360582040362432331, 360582039622842393, 360582038883117921, 360582038427525371]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564349230379402, 360564371659963913⟩, ⟨1048013027535323700, 1048912816542256014⟩, true⟩

def words07 : List Nat := [360582038216425527, 360582038089034386, 360582037961564432, 360582037689998388, 360582037424906161, 360582037029811403, 360582036634486347, 360582036523094962, 360582036369129237, 360582036072502517]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360576514603045139, 360576537040476594⟩, ⟨325533478361351328, 326433733358410098⟩, true⟩

def words08 : List Nat := [360582035775711137, 360582035359208711, 360582035088130136, 360582034995539957, 360582034902884610, 360582034544161259, 360582034055556253, 360582033850882791, 360582033645960956, 360582033483200259]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584536916878965, 360584559362224443⟩, ⟨(-150970974602319062), (-150070249553100398)⟩, true⟩

def words09 : List Nat := [360582033391399895, 360582033157855196, 360582032973397293, 360582033199703169, 360582033233830917, 360582033268081734, 360582033268824800, 360582033123917539, 360582032926082665, 360582032969578645]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk593B

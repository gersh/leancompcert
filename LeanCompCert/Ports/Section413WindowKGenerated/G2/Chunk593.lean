import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk593

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603769589219357, 360603791956005047⟩, ⟨(-1290515105781160513), (-1289619043252415617)⟩, true⟩

def state01 : KState := ⟨⟨360592991702527190, 360593014077209933⟩, ⟨(-651503147571096291), (-650606616708164975)⟩, true⟩

def words00 : List Nat := [360582045098338198, 360582045099167070, 360582045128447096, 360582045229161995, 360582045229856084, 360582045200406917, 360582045088642291, 360582044811542521, 360582044534293225, 360582044668218209]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564233632015895, 360564256014516599⟩, ⟨1054231718110264855, 1055128712695665069⟩, true⟩

def words01 : List Nat := [360582044761808713, 360582044855548571, 360582044856288971, 360582044752909066, 360582044461273125, 360582044097041125, 360582043732579049, 360582043499282191, 360582043378797664, 360582043079801422]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588901981281369, 360588924371601352⟩, ⟨(-409241006991028773), (-408343548526671553)⟩, true⟩

def words02 : List Nat := [360582042780627318, 360582042766642230, 360582042872254260, 360582042978017203, 360582042978795808, 360582042826633080, 360582042391192567, 360582042120765018, 360582041850094757, 360582041906304515]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577794782512793, 360577817180740190⟩, ⟨249895243435493596, 250793171084276530⟩, true⟩

def words03 : List Nat := [360582041907043088, 360582041880911684, 360582042111738193, 360582042601952039, 360582043019203652, 360582043436576738, 360582043673096537, 360582043673925918, 360582043627341272, 360582043557064496]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568143098033672, 360568165504071257⟩, ⟨822661495883649707, 823559887027290063⟩, true⟩

def words04 : List Nat := [360582043699330224, 360582043700159621, 360582043630695826, 360582043396711234, 360582043162607140, 360582042686118660, 360582042440278077, 360582042288887805, 360582042137411588, 360582041829042231]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk593

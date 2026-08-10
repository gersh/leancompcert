import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk581A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583366306703961, 360583387742484608⟩, ⟨(-84961465662824329), (-84120055054226781)⟩, true⟩

def state01 : KState := ⟨⟨360600261546510309, 360600282990015267⟩, ⟨(-1066770637645751634), (-1065928778216992110)⟩, true⟩

def words00 : List Nat := [360581939918642218, 360581939785856311, 360581939895300343, 360581940054972667, 360581940138792414, 360581940139605856, 360581940124034138, 360581939882826794, 360581939695707375, 360581940012296471]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584821253100595, 360584842704237084⟩, ⟨(-169355189570528488), (-168512886634476996)⟩, true⟩

def words01 : List Nat := [360581940624828133, 360581941237494182, 360581941618313329, 360581942019143120, 360581942290167229, 360581942561397694, 360581943056770286, 360581943256939999, 360581943307550081, 360581943358275479]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580872149949317, 360580893608759180⟩, ⟨60074744139481680, 60917493089763756⟩, true⟩

def words02 : List Nat := [360581943358945297, 360581943289328282, 360581943289989233, 360581943271268133, 360581943252480419, 360581942989263068, 360581942430619381, 360581942042327649, 360581941653795791, 360581941561504575]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360569449816475357, 360569471283019198⟩, ⟨724109923992892052, 724953122556769190⟩, true⟩

def words03 : List Nat := [360581941544207461, 360581941378017714, 360581941250131340, 360581941437376516, 360581941438072164, 360581941343408868, 360581941248656057, 360581941004660118, 360581940590506171, 360581940376974423]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585758448421710, 360585779922619981⟩, ⟨(-224136800977370318), (-223293157346639398)⟩, true⟩

def words04 : List Nat := [360581940163167831, 360581940154560614, 360581940153268567, 360581940002807381, 360581939852218299, 360581939567888473, 360581939745134976, 360581939982148076, 360581939982894271, 360581940037538957]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk581A

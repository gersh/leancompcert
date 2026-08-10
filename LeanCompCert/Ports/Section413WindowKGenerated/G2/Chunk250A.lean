import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk250A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360536683811519857, 360536687511688331⟩, ⟨1179395031823839449, 1179457610235706293⟩, true⟩

def state01 : KState := ⟨⟨360571232642946366, 360571236346197110⟩, ⟨315432710670963022, 315495366154870304⟩, true⟩

def words00 : List Nat := [360583863929305755, 360583862769941857, 360583862410093720, 360583862282116266, 360583862154117285, 360583860677299146, 360583857611657150, 360583855059557622, 360583852507566988, 360583851114935810]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360608753510529154, 360608757216898438⟩, ⟨(-623243465492454417), (-623180731998655461)⟩, true⟩

def words01 : List Nat := [360583850610865841, 360583848853480095, 360583847096170939, 360583848013668466, 360583848685739740, 360583849357810591, 360583849358102077, 360583849115413963, 360583849913085553, 360583850908917197]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570100707919132, 360570104417366615⟩, ⟨343958166243345319, 344020976769052329⟩, true⟩

def words02 : List Nat := [360583853062744895, 360583853629201942, 360583853629493914, 360583853216452496, 360583852803397763, 360583850804232431, 360583849885615946, 360583849803869586, 360583849722097170, 360583848763222351]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360635799193439792, 360635802905977948⟩, ⟨(-1300736380308034760), (-1300673492407363954)⟩, true⟩

def words03 : List Nat := [360583849257014468, 360583850299917754, 360583852934178942, 360583853982324884, 360583853982626428, 360583853687046992, 360583854686806565, 360583857001284306, 360583859076070579, 360583861150760211]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360634815305218299, 360634819020870332⟩, ⟨(-1276396706482705889), (-1276333740595215781)⟩, true⟩

def words04 : List Nat := [360583862126774368, 360583862431078931, 360583863871753672, 360583865312408782, 360583866344923344, 360583867420615939, 360583867420912527, 360583867169129231, 360583867573766863, 360583869608048680]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk250A

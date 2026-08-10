import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk818A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603881693134781, 360603925351470571⟩, ⟨(-1773027916428929691), (-1770616038523206895)⟩, true⟩

def state01 : KState := ⟨⟨360582223195111089, 360582266864632893⟩, ⟨(-1250323704776844), 1162469270054450⟩, true⟩

def words00 : List Nat := [360582280114707527, 360582280289925480, 360582280588173119, 360582280886761053, 360582281147540201, 360582281259432772, 360582281260484675, 360582281233463097, 360582281206240465, 360582281074011576]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577651756841906, 360577695437393860⟩, ⟨372772013294410580, 375185708703222312⟩, true⟩

def words01 : List Nat := [360582281144610545, 360582281215604723, 360582281216649022, 360582281212825043, 360582281143598229, 360582281037255968, 360582280972167922, 360582280992377163, 360582280993431304, 360582280938600206]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584852551867293, 360584896243499676⟩, ⟨(-216438398262749151), (-214023796198796217)⟩, true⟩

def words02 : List Nat := [360582280883507303, 360582280967872635, 360582281053366811, 360582281139066944, 360582281140149340, 360582281099672378, 360582280947166646, 360582280897654142, 360582280847793453, 360582280806853432]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584656149879116, 360584699852677010⟩, ⟨(-200416488764227306), (-198000972973192622)⟩, true⟩

def words03 : List Nat := [360582280807897901, 360582280766253042, 360582280724386718, 360582280749502799, 360582280750488654, 360582280730428690, 360582280710270073, 360582280573721399, 360582280484602126, 360582280515511370]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591122762826165, 360591166476654045⟩, ⟨(-729700193010758712), (-727283774469094942)⟩, true⟩

def words04 : List Nat := [360582280664287958, 360582280699402441, 360582280700447058, 360582280660831589, 360582280621004701, 360582280544096035, 360582280687716909, 360582280834805126, 360582280907027496, 360582281016800542]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk818A

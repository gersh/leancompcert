import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk836A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505768265310683, 362505873421048638⟩, ⟨(-1724108457855493110), (-1718172527897800664)⟩, true⟩

def state01 : KState := ⟨⟨362491059592360182, 362491164774294338⟩, ⟨(-494456863407866929), (-488518743311380971)⟩, true⟩

def words00 : List Nat := [371285321583548527, 371285321613159006, 371285321713669819, 371285321815640880, 371285321933096358, 371285321936004487, 371285321907558219, 371285321873593085, 371285321944219639, 371285322017440439]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477604659039348, 362477709867043320⟩, ⟨630610645257632130, 636550945181963098⟩, true⟩

def words01 : List Nat := [371285322162682803, 371285322309062600, 371285322445327925, 371285322448228466, 371285322409023929, 371285322378654375, 371285322455850427, 371285322458750859, 371285322379448617, 371285322291644875]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481320918690972, 362481426152691089⟩, ⟨319910900055800039, 325853373910311177⟩, true⟩

def words02 : List Nat := [371285322254559795, 371285322272313107, 371285322378334700, 371285322485555240, 371285322560774114, 371285322563674984, 371285322458518370, 371285322472490027, 371285322519099689, 371285322522102907]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486614013846951, 362486719274298933⟩, ⟨(-122793553204685984), (-116848867050703238)⟩, true⟩

def words03 : List Nat := [371285322477681776, 371285322427419340, 371285322395976806, 371285322399174845, 371285322356965642, 371285322349384077, 371285322340812114, 371285322332969732, 371285322225388054, 371285322245723824]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487910683205763, 362488015969547516⟩, ⟨(-231237825245331089), (-225290973536910877)⟩, true⟩

def words04 : List Nat := [371285322407343386, 371285322433044575, 371285322435251964, 371285322429382388, 371285322457080884, 371285322460311673, 371285322518647865, 371285322614519093, 371285322709182857, 371285322744439187]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk836A

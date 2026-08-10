import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk415A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360553495649003529, 360553506289303782⟩, ⟨1200637101816455792, 1200935531961557096⟩, true⟩

def state01 : KState := ⟨⟨360564002461854597, 360564013107483578⟩, ⟨764526910999774672, 764825562313790858⟩, true⟩

def words00 : List Nat := [360582443798060128, 360582443489976274, 360582443471626322, 360582443159488604, 360582442847322082, 360582442043523485, 360582440662076011, 360582439859744802, 360582439057283963, 360582438199324431]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562326585643850, 360562337236641641⟩, ⟨834126183858247643, 834425058058192517⟩, true⟩

def words01 : List Nat := [360582437755966681, 360582436959314484, 360582436162592820, 360582436295688637, 360582436296162574, 360582436253027043, 360582436209845431, 360582435724954575, 360582434662671965, 360582434179273101]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574216245597608, 360574226901907309⟩, ⟨340432134719245522, 340731229496556476⟩, true⟩

def words02 : List Nat := [360582433790333065, 360582433790899956, 360582433719114221, 360582433357367270, 360582432995539811, 360582432228105040, 360582431755326152, 360582431730143498, 360582431704900143, 360582431362044477]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360607651594020440, 360607662255667135⟩, ⟨(-1048524411816605671), (-1048225095368291543)⟩, true⟩

def words03 : List Nat := [360582431164959746, 360582430701092151, 360582430237081865, 360582430109527005, 360582429732715482, 360582428851291991, 360582427969799201, 360582427533150453, 360582428141087001, 360582428749122558]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577926673817649, 360577937340838092⟩, ⟨186175431306267027, 186474971006798697⟩, true⟩

def words04 : List Nat := [360582428990905387, 360582428991469937, 360582428899479427, 360582429142890852, 360582429143371555, 360582428987097861, 360582428254318151, 360582427079009038, 360582425903644168, 360582425306445958]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk415A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk605A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360630036762527386, 360630060080779121⟩, ⟨(-2887922326053495192), (-2886969268746880298)⟩, true⟩

def state01 : KState := ⟨⟨360618163738112579, 360618187064433455⟩, ⟨(-2169708072403091693), (-2168754526873288975)⟩, true⟩

def words00 : List Nat := [360582342910935355, 360582343392454751, 360582343965532318, 360582344538837669, 360582345041961226, 360582345272889752, 360582345359344077, 360582345445894976, 360582345805380047, 360582346398655774]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571481770523599, 360571505104819290⟩, ⟨655286174890873872, 656240203016177050⟩, true⟩

def words01 : List Nat := [360582347032730018, 360582347666941871, 360582348127624520, 360582348393239739, 360582348423192601, 360582348453360609, 360582348684353360, 360582348685200537, 360582348644035083, 360582348465741567]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360607386194860689, 360607409537163408⟩, ⟨(-1517740673734278743), (-1516786160984337171)⟩, true⟩

def words02 : List Nat := [360582348381095808, 360582348730705351, 360582349226475383, 360582349722390887, 360582349983324903, 360582350063931665, 360582350417316671, 360582350770943170, 360582351116313092, 360582351531166740]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360597355619909403, 360597378970277656⟩, ⟨(-910550768476581339), (-909595767480411101)⟩, true⟩

def words03 : List Nat := [360582351808710565, 360582352086338378, 360582352404976060, 360582352912976515, 360582353350918206, 360582353789000075, 360582354037141237, 360582354037988677, 360582354262217136, 360582354511357579]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593880061550708, 360593903419907670⟩, ⟨(-700238660341192136), (-699283175668362708)⟩, true⟩

def words04 : List Nat := [360582354840455875, 360582354897705413, 360582354898481055, 360582354748196020, 360582354597771559, 360582354377833359, 360582354429065791, 360582354565077331, 360582354565832181, 360582354755547571]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk605A

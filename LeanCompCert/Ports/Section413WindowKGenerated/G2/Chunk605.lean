import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk605

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

def state06 : KState := ⟨⟨360612106732193937, 360612130098549529⟩, ⟨(-1803929165065348569), (-1802973196035889811)⟩, true⟩

def words05 : List Nat := [360582355162696337, 360582355570089874, 360582356095304277, 360582356686593311, 360582357004917098, 360582357323291412, 360582357554035916, 360582357921156654, 360582358413457441, 360582358905933227]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608953864022641, 360608977238456265⟩, ⟨(-1613109315449773700), (-1612152857175072082)⟩, true⟩

def words06 : List Nat := [360582359259867117, 360582359403086259, 360582359738291800, 360582360073751497, 360582360339373288, 360582360563166977, 360582360615148243, 360582360667217142, 360582360878603490, 360582361319003473]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571118548542624, 360571141930971436⟩, ⟨678739907572713489, 679696850156242975⟩, true⟩

def words07 : List Nat := [360582361643570553, 360582361968277465, 360582362127260709, 360582362128109363, 360582362126880428, 360582362057385155, 360582361987648011, 360582361959407004, 360582361937850553, 360582361753522712]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602946196877656, 360602969587308723⟩, ⟨(-1249552955395120776), (-1248595527996684200)⟩, true⟩

def words08 : List Nat := [360582361569005172, 360582361668594545, 360582361990501616, 360582362312560437, 360582362371112147, 360582362371960357, 360582362158846213, 360582362115305376, 360582362299287518, 360582362640270439]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569578272667014, 360569601671182998⟩, ⟨772421383902646679, 773379301206915753⟩, true⟩

def words09 : List Nat := [360582362817329268, 360582362994488175, 360582363152306702, 360582363446288970, 360582363670556462, 360582363894955113, 360582363983023875, 360582363983872633, 360582363915485815, 360582363705856380]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk605

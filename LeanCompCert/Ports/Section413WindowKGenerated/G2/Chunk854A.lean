import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk854A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572167959506236, 360572215704530785⟩, ⟨866969489332376287, 869723070691688889⟩, true⟩

def state01 : KState := ⟨⟨360552174030971432, 360552221787697115⟩, ⟨2574447784838959918, 2577202365529845674⟩, true⟩

def words00 : List Nat := [360582399697283020, 360582399509257689, 360582399183926797, 360582398940169887, 360582398696087992, 360582398361135808, 360582397889008292, 360582397312359626, 360582396735485876, 360582396268033491]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 85400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 85400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360541699651508320, 360541747419778255⟩, ⟨3469188862077615343, 3471944428823276525⟩, true⟩

def words01 : List Nat := [360582395915740067, 360582395700645694, 360582395485422525, 360582395190589705, 360582394899164028, 360582394518869165, 360582394138222742, 360582393868918134, 360582393462465135, 360582392987898406]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 85410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 85400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565771117392708, 360565818897273999⟩, ⟨1412826830115810735, 1415583388759059195⟩, true⟩

def words02 : List Nat := [360582392513081670, 360582392035010302, 360582391643442616, 360582391292921392, 360582390942314843, 360582390454194359, 360582389952133389, 360582389587385741, 360582389222248316, 360582388994297985]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 85420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 85400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556934106391196, 360556981897954514⟩, ⟨2167819239057775104, 2170576795755242478⟩, true⟩

def words03 : List Nat := [360582388801432885, 360582388539958817, 360582388278255851, 360582388096523784, 360582387997694423, 360582387805961626, 360582387614109995, 360582387318086933, 360582386884858286, 360582386588916069]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 85430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 85400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568677348711689, 360568725151861080⟩, ⟨1164440683548866357, 1167199230217061511⟩, true⟩

def words04 : List Nat := [360582386292572903, 360582386083141734, 360582385934204377, 360582385702403967, 360582385470409627, 360582385166448714, 360582384948226027, 360582384867099421, 360582384785856845, 360582384592823246]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 85440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 85400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk854A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk472

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471540561361680, 362471572602493152⟩, ⟨649289500247686452, 650311277758514780⟩, true⟩

def state01 : KState := ⟨⟨362466807070629968, 362466839125810970⟩, ⟨872737495578336891, 873759936300297607⟩, true⟩

def words00 : List Nat := [371285350092996198, 371285349848333691, 371285349378114698, 371285349205946202, 371285349033323172, 371285348792178656, 371285347953239768, 371285347562788276, 371285347171498606, 371285347067694052]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362462821390327800, 362462853459783952⟩, ⟨1060971539549474292, 1061994654273526694⟩, true⟩

def words01 : List Nat := [371285346676841328, 371285346287715599, 371285345897970639, 371285345882420776, 371285345672525715, 371285345476121671, 371285345279168821, 371285345083854930, 371285344291088889, 371285343816714777]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362462553812770098, 362462585896214123⟩, ⟨1073682642237588953, 1074706417542660973⟩, true⟩

def words02 : List Nat := [371285343341501216, 371285343314088826, 371285342913258422, 371285342433761471, 371285341953672541, 371285341610075844, 371285341086661754, 371285340959059758, 371285340830974613, 371285340637216509]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510880131168107, 362510912228818798⟩, ⟨(-1208992682829889907), (-1207968236474883841)⟩, true⟩

def words03 : List Nat := [371285340156506556, 371285340081324717, 371285340322308200, 371285340356955374, 371285340358171250, 371285340303847714, 371285340639724337, 371285340807519200, 371285341349893658, 371285341892956414]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481830013141892, 362481862124997509⟩, ⟨163420013175750335, 164445130641554769⟩, true⟩

def words04 : List Nat := [371285342407547100, 371285342600004111, 371285342857240705, 371285343115241547, 371285343387638004, 371285343389208403, 371285343065438296, 371285342743690380, 371285342443380288, 371285342445222728]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362453156352980652, 362453188478948894⟩, ⟨1518529053842834232, 1519554838202984290⟩, true⟩

def words05 : List Nat := [371285342745586796, 371285343120214547, 371285343477175126, 371285343478745681, 371285343239606224, 371285343081878083, 371285342923336970, 371285342881539990, 371285342243423824, 371285341564818615]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469244004712463, 362469276144744984⟩, ⟨758198876427612574, 759225325536805534⟩, true⟩

def words06 : List Nat := [371285340885554695, 371285340612527804, 371285340114262545, 371285340015300600, 371285339915804802, 371285339702302495, 371285338892609810, 371285338315697768, 371285337737988468, 371285337607100322]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481190270569819, 362481222424949392⟩, ⟨193399333949512700, 194426461316306264⟩, true⟩

def words07 : List Nat := [371285337268521720, 371285336838388359, 371285336407618291, 371285336319399197, 371285336006072805, 371285335785455654, 371285335564347504, 371285335276742557, 371285334744759891, 371285334659748807]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362466280313171682, 362466312481532705⟩, ⟨898452409131115482, 899480197614270020⟩, true⟩

def words08 : List Nat := [371285334783822061, 371285334785394169, 371285334486320720, 371285334189246662, 371285333891618299, 371285333624165756, 371285333156012314, 371285333134430625, 371285333112312027, 371285332997447577]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498751473385074, 362498783655968276⟩, ⟨(-637213310253958201), (-636184849132616057)⟩, true⟩

def words09 : List Nat := [371285332596315321, 371285332499953433, 371285332750345595, 371285332795200919, 371285332796429201, 371285332774091858, 371285333172791132, 371285333371944991, 371285333657392842, 371285333943506962]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk472

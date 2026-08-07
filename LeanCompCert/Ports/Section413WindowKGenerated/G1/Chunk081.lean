import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk081

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362456952120407400, 362456952929920475⟩, ⟨217861995040066886, 217866435267174046⟩, true⟩

def state01 : KState := ⟨⟨362358914949783320, 362358915761367424⟩, ⟨1012830533169000689, 1012834990182463449⟩, true⟩

def words00 : List Nat := [371283858532494347, 371283858532726997, 371283850143557672, 371283840641026150, 371283831140749366, 371283826400397017, 371283816243437135, 371283812441523994, 371283808640474880, 371283802936482401]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489060578602204, 362489061392298979⟩, ⟨(-43385487984931988), (-43381013827284194)⟩, true⟩

def words01 : List Nat := [371283787539381073, 371283787261402003, 371283789898655814, 371283789898888851, 371283772650843375, 371283752716009566, 371283732785995950, 371283727960501125, 371283718902643432, 371283719560772408]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362385133081760335, 362385133897560331⟩, ⟨800952392846388371, 800956884093125697⟩, true⟩

def words02 : List Nat := [371283720237425447, 371283720237658846, 371283704645628837, 371283704134524334, 371283706012627794, 371283706012861753, 371283693257436925, 371283677158192381, 371283661062812697, 371283652579490605]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362414593508531475, 362414594326432978⟩, ⟨561733945318018192, 561738453660803266⟩, true⟩

def words03 : List Nat := [371283640494279782, 371283640525582476, 371283640591788190, 371283640592025832, 371283629031728401, 371283622199479871, 371283620973047363, 371283620973282133, 371283612443097336, 371283603964474846]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362450618926292711, 362450619746289768⟩, ⟨268446679526158288, 268451204937504934⟩, true⟩

def words04 : List Nat := [371283595487835549, 371283593265571276, 371283586164993031, 371283587352672329, 371283587352855257, 371283586406350197, 371283565470330082, 371283559504440188, 371283558544199077, 371283558544441610]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362403160324426859, 362403161146559865⟩, ⟨655640510293502817, 655645053123457833⟩, true⟩

def words05 : List Nat := [371283554503544789, 371283548020879933, 371283547140139046, 371283547140399437, 371283545414238150, 371283543909886260, 371283542405826947, 371283540992620211, 371283519652593684, 371283509805030877]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362452894663511432, 362452895487736735⟩, ⟨250040042775786680, 250044602689825538⟩, true⟩

def words06 : List Nat := [371283505018525045, 371283505018765119, 371283502454524738, 371283499726313968, 371283496998683723, 371283495428774262, 371283492166625158, 371283497978611006, 371283500702020689, 371283500702264254]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362600850654271509, 362600851480619291⟩, ⟨(-959454588443397983), (-959450011177946971)⟩, true⟩

def words07 : List Nat := [371283508088158552, 371283519217039080, 371283537977033309, 371283540261394240, 371283540601731408, 371283540942065003, 371283545472334530, 371283545472593594, 371283559302952209, 371283573640357961]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362422620972676334, 362422621801152688⟩, ⟨498837393920842471, 498841988608571425⟩, true⟩

def words08 : List Nat := [371283587180330669, 371283587180566011, 371283580896091635, 371283580084556732, 371283583158978562, 371283583159213963, 371283567244581812, 371283551415009385, 371283535589210285, 371283530468870463]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362307994595530082, 362307995426127064⟩, ⟨1438954377026962034, 1438958989093645964⟩, true⟩

def words09 : List Nat := [371283530395826253, 371283537757130627, 371283545211989161, 371283545212225357, 371283537752218550, 371283530076303797, 371283522402146396, 371283520886117619, 371283499632360427, 371283478229675070]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk081

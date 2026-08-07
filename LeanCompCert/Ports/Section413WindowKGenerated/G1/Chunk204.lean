import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk204

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486472471047172, 362486478052432662⟩, ⟨(-32238832651558332), (-32161827598327704)⟩, true⟩

def state01 : KState := ⟨⟨362463039094402457, 362463044681426219⟩, ⟨445896873381992430, 445973993485772780⟩, true⟩

def words00 : List Nat := [371284903346521312, 371284903347155173, 371284902082849464, 371284900798129999, 371284899513311342, 371284897968811142, 371284895539518063, 371284895504432018, 371284895469130891, 371284895440538702]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362518379629052856, 362518385221812824⟩, ⟨(-683742422996427296), (-683665185788214238)⟩, true⟩

def words01 : List Nat := [371284895692704582, 371284897015619838, 371284900334625534, 371284900877648139, 371284901007855415, 371284901138260683, 371284902776920203, 371284903405408664, 371284905045505137, 371284906685708412]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473418917564490, 362473424516052050⟩, ⟨234403761227842830, 234481115422859006⟩, true⟩

def words02 : List Nat := [371284908306171804, 371284908306806453, 371284906747234727, 371284906758034638, 371284907237656357, 371284907238301954, 371284905724919029, 371284903748518879, 371284901809273352, 371284901810003243]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472572644546403, 362472578248764681⟩, ⟨251869867014552206, 251947338317379878⟩, true⟩

def words03 : List Nat := [371284903074456561, 371284904900755078, 371284906305222009, 371284906305858589, 371284905286178566, 371284904702534013, 371284905641949849, 371284905642589169, 371284905041826250, 371284904439484710]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467381050586884, 362467386660489836⟩, ⟨358367010894025564, 358444598420692234⟩, true⟩

def words04 : List Nat := [371284905619581080, 371284906208262289, 371284909182134486, 371284912155968795, 371284914721429879, 371284914722065286, 371284914104680846, 371284913999012740, 371284914513055099, 371284914513713342]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483087865099565, 362483093480780560⟩, ⟨37151498090932082, 37229203808100990⟩, true⟩

def words05 : List Nat := [371284913657124198, 371284912475223487, 371284912287999253, 371284912434843910, 371284913319694550, 371284914204706584, 371284915072430303, 371284915073066216, 371284913178114505, 371284913089959842]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362453603963673985, 362453609585028628⟩, ⟨640506679785548850, 640584501614798580⟩, true⟩

def words06 : List Nat := [371284913508405135, 371284913509044200, 371284911750565239, 371284909876480896, 371284908002328989, 371284906866992085, 371284904556420439, 371284904171248911, 371284903785892981, 371284903405332234]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362529773259878602, 362529778886986123⟩, ⟨(-919155379010150028), (-919077439390341952)⟩, true⟩

def words07 : List Nat := [371284901877076985, 371284901564037917, 371284902793070624, 371284902793707721, 371284901788813038, 371284900417460408, 371284900051011672, 371284900051712676, 371284902058167425, 371284904250035274]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503552561168984, 362503558194025922⟩, ⟨(-381949464643902647), (-381871407246305503)⟩, true⟩

def words08 : List Nat := [371284906446205187, 371284907575478614, 371284911080227220, 371284914584961976, 371284918246001250, 371284918736920619, 371284919232894897, 371284919729043780, 371284921228573800, 371284922138818939]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472278820135650, 362472284458720575⟩, ⟨259159093470662804, 259237268263208830⟩, true⟩

def words09 : List Nat := [371284925057419750, 371284927975988035, 371284930329892461, 371284930330529542, 371284929517091965, 371284929442470567, 371284931418130494, 371284931418768001, 371284930795308091, 371284930179123659]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk204

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk405

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471875535361685, 362471898834121805⟩, ⟨538015691830519618, 538653307745530638⟩, true⟩

def state01 : KState := ⟨⟨362477102623544754, 362477125934154562⟩, ⟨326388384743753200, 327026480632290202⟩, true⟩

def words00 : List Nat := [371285198770564162, 371285198771925149, 371285198620351230, 371285198406769800, 371285198192678659, 371285198163126412, 371285198169623662, 371285198478271322, 371285198667427670, 371285198668803595]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499834238443560, 362499857561080527⟩, ⟨(-594637830758934224), (-593999247588991812)⟩, true⟩

def words01 : List Nat := [371285198656874600, 371285198844913746, 371285199207484307, 371285199208814259, 371285198877867008, 371285198427827981, 371285198033241619, 371285198034719887, 371285198150701003, 371285198513979296]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476892127886334, 362476915462540240⟩, ⟨334966935345576498, 335606005503043596⟩, true⟩

def words02 : List Nat := [371285198874319985, 371285198875649795, 371285198424893270, 371285198221943165, 371285198018351956, 371285198005485486, 371285197336403048, 371285196653956448, 371285195970982007, 371285195896922255]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362452582231358180, 362452605577961462⟩, ⟨1320515603359095174, 1321155157887742320⟩, true⟩

def words03 : List Nat := [371285196097459480, 371285196502803995, 371285196835309188, 371285196836645896, 371285196589932308, 371285196347128964, 371285196110247132, 371285196111577590, 371285195308784326, 371285194506375072]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476307316908097, 362476330675427611⟩, ⟨358706111177036437, 359346148849165419⟩, true⟩

def words04 : List Nat := [371285193703427040, 371285193415206715, 371285192948866964, 371285193020652728, 371285193021695158, 371285192942668660, 371285192464852545, 371285192387099233, 371285192477965761, 371285192479344977]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487948758191880, 362487972128865398⟩, ⟨(-113428408841401195), (-112787878263837749)⟩, true⟩

def words05 : List Nat := [371285192261822485, 371285191925091261, 371285191789572280, 371285191791053445, 371285191776818163, 371285191862442428, 371285191863444329, 371285191830319058, 371285191360962152, 371285191431193649]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478186426056791, 362478209808569686⟩, ⟨282632981823494579, 283273992669309899⟩, true⟩

def words06 : List Nat := [371285192010467469, 371285192011802362, 371285191970220052, 371285191928757740, 371285191886818816, 371285191851697039, 371285191727105929, 371285191943180206, 371285192158502042, 371285192159880244]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486410822968399, 362486434217526644⟩, ⟨(-51008824665737242), (-50367325080037814)⟩, true⟩

def words07 : List Nat := [371285192260023972, 371285192532974590, 371285193204461230, 371285193205792918, 371285193068521678, 371285192824034217, 371285192939791093, 371285192998596741, 371285193030112622, 371285193062181038]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488885227605401, 362488908634189347⟩, ⟨(-151521564599643949), (-150879576951106369)⟩, true⟩

def words08 : List Nat := [371285193073604951, 371285193074937004, 371285192353588071, 371285192239561061, 371285192192782584, 371285192194144110, 371285191912513087, 371285191607378648, 371285191471350884, 371285191564470663]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473240401436787, 362473263820039954⟩, ⟨483676846797162097, 484319322365680569⟩, true⟩

def words09 : List Nat := [371285192263271337, 371285192962596965, 371285193542562582, 371285193543894919, 371285193315667324, 371285193152106904, 371285193428947336, 371285193430280206, 371285193159677496, 371285192867388863]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk405

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk954A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486910689817846, 362487049029307865⟩, ⟨(-183335404620677371), (-174424884185055847)⟩, true⟩

def state01 : KState := ⟨⟨362479373248156119, 362479511617469659⟩, ⟨535772361584276788, 544685727335503210⟩, true⟩

def words00 : List Nat := [371285220826812439, 371285220830156449, 371285220815373712, 371285220759117352, 371285220701594940, 371285220678478125, 371285220599222459, 371285220570815844, 371285220541258323, 371285220513050159]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498498294631673, 362498636694118306⟩, ⟨(-1289035226262324885), (-1280118981541700571)⟩, true⟩

def words01 : List Nat := [371285220494473851, 371285220537430353, 371285220688651734, 371285220742792030, 371285220779564760, 371285220817408814, 371285220887672407, 371285220922047574, 371285221064912288, 371285221209250807]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484574885036630, 362484713314691266⟩, ⟨39559635749185535, 48478759253013131⟩, true⟩

def words02 : List Nat := [371285221339349606, 371285221342694565, 371285221392288254, 371285221462587586, 371285221532295924, 371285221535640937, 371285221459080543, 371285221375791374, 371285221314220166, 371285221318036682]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478543077350663, 362478681537203737⟩, ⟨615212537022033539, 624134542516400371⟩, true⟩

def words03 : List Nat := [371285221355136853, 371285221398912500, 371285221441396614, 371285221444741891, 371285221340657446, 371285221271310751, 371285221207539306, 371285221210952516, 371285221150773109, 371285221086056592]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490373845387318, 362490512335151103⟩, ⟨(-513941460532787406), (-505016600207580682)⟩, true⟩

def words04 : List Nat := [371285221061189411, 371285221064876481, 371285221150464763, 371285221250673966, 371285221318279411, 371285221321641157, 371285221299812049, 371285221319693773, 371285221429632702, 371285221488536531]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk954A

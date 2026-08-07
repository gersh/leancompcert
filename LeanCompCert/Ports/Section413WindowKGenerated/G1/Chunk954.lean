import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk954

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

def state06 : KState := ⟨⟨362488182931246453, 362488321451509010⟩, ⟨(-304779877427125870), (-295852105841941146)⟩, true⟩

def words05 : List Nat := [371285221546070665, 371285221604768149, 371285221756439580, 371285221854628934, 371285221962784742, 371285222072269772, 371285222178100329, 371285222186695975, 371285222221481958, 371285222258059938]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486300296843108, 362486438846864335⟩, ⟨(-125028055395100168), (-116097442888309882)⟩, true⟩

def words06 : List Nat := [371285222402655037, 371285222415602529, 371285222428066094, 371285222441666826, 371285222479779546, 371285222483531938, 371285222587146760, 371285222696348452, 371285222781360435, 371285222797562576]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498744043785699, 362498882624170579⟩, ⟨(-1313110311606177332), (-1304176800141093922)⟩, true⟩

def words07 : List Nat := [371285222922415187, 371285223049119869, 371285223199721666, 371285223205066982, 371285223207665208, 371285223198524008, 371285223275907434, 371285223312826113, 371285223458154410, 371285223605097245]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482668297520585, 362482806908080323⟩, ⟨221872183227088221, 230808575943652667⟩, true⟩

def words08 : List Nat := [371285223747869910, 371285223751216713, 371285223851270284, 371285223959041365, 371285224088079338, 371285224091426282, 371285224074392808, 371285224037342054, 371285224001052041, 371285224004906626]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478425183066687, 362478563823718106⟩, ⟨627099626914553416, 636038893238049860⟩, true⟩

def words09 : List Nat := [371285224012332160, 371285224046386954, 371285224075241152, 371285224078654307, 371285224037306901, 371285224023884967, 371285224045212947, 371285224048576424, 371285223982846661, 371285223916841018]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk954

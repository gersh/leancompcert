import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk896

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487865290354009, 362487986729302087⟩, ⟨(-262438710844985301), (-255092045937495463)⟩, true⟩

def state01 : KState := ⟨⟨362479563340932257, 362479684808058999⟩, ⟨481439504342004854, 488788694200511310⟩, true⟩

def words00 : List Nat := [371285139785575447, 371285139788701108, 371285139678749902, 371285139688696955, 371285139735072287, 371285139738218891, 371285139673293737, 371285139570235177, 371285139465884328, 371285139430246261]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477036164139407, 362477157659351827⟩, ⟨707979750863666903, 715331457627153623⟩, true⟩

def words01 : List Nat := [371285139435072124, 371285139502012255, 371285139566242217, 371285139569424402, 371285139560416836, 371285139577589217, 371285139656737531, 371285139659863560, 371285139573293059, 371285139487711872]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480574316529294, 362480695839775805⟩, ⟨390870449042804911, 398224668361017013⟩, true⟩

def words02 : List Nat := [371285139400809459, 371285139347897807, 371285139247363670, 371285139217463494, 371285139186556145, 371285139134222974, 371285138936289678, 371285138864436448, 371285138820677882, 371285138823914610]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474286158938019, 362474407710702801⟩, ⟨954550543851746491, 961907319404968377⟩, true⟩

def words03 : List Nat := [371285138776707069, 371285138720239298, 371285138726935340, 371285138732781292, 371285138742244755, 371285138752828899, 371285138762225605, 371285138765352369, 371285138608703727, 371285138492936235]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476008807740833, 362476130387401169⟩, ⟨800142745047551485, 807502021301618615⟩, true⟩

def words04 : List Nat := [371285138375353870, 371285138337423434, 371285138218313705, 371285138100087168, 371285137980692843, 371285137900527533, 371285137763659998, 371285137738657394, 371285137712604536, 371285137660366051]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500142306515622, 362500263914379367⟩, ⟨(-1363557072186910731), (-1356195267352349375)⟩, true⟩

def words05 : List Nat := [371285137562017302, 371285137563169050, 371285137684481564, 371285137687613505, 371285137677415237, 371285137649550227, 371285137713283449, 371285137761177664, 371285137932004017, 371285138104190407]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485935855485019, 362486057491604422⟩, ⟨(-89794331802443954), (-82429993426123764)⟩, true⟩

def words06 : List Nat := [371285138255067559, 371285138258195338, 371285138304206615, 371285138355726405, 371285138432981760, 371285138436109731, 371285138361571228, 371285138277337557, 371285138228538201, 371285138242422121]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474073791629201, 362474195455940639⟩, ⟨974007794345520753, 981374660840933893⟩, true⟩

def words07 : List Nat := [371285138379071196, 371285138517042119, 371285138649060416, 371285138662790071, 371285138684081548, 371285138706914814, 371285138757654861, 371285138760782929, 371285138645997407, 371285138527537885]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478854060769711, 362478975753050264⟩, ⟨545314706424104981, 552684081335774899⟩, true⟩

def words08 : List Nat := [371285138409875643, 371285138413323170, 371285138355683817, 371285138349389202, 371285138342112783, 371285138314506157, 371285138120226802, 371285138010299984, 371285137909264496, 371285137912503222]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485627219991597, 362485748940813365⟩, ⟨(-62205761074744615), (-54833826162161167)⟩, true⟩

def words09 : List Nat := [371285137846177986, 371285137757116016, 371285137686457419, 371285137689964819, 371285137682077991, 371285137699436087, 371285137706927960, 371285137710112601, 371285137634533685, 371285137645218421]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk896

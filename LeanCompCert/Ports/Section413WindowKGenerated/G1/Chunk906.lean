import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk906

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491068060007889, 362491192331146309⟩, ⟨(-557173755313407576), (-549571906955919586)⟩, true⟩

def state01 : KState := ⟨⟨362481309939468525, 362481434238805047⟩, ⟨326942481777357481, 334546885029909069⟩, true⟩

def words00 : List Nat := [371285126590235533, 371285126593398040, 371285126552579449, 371285126512977699, 371285126472193985, 371285126469908444, 371285126405493858, 371285126404737194, 371285126402810493, 371285126401756487]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496073055379211, 362496197383246723⟩, ⟨(-1010845417293153887), (-1003238428701836203)⟩, true⟩

def words01 : List Nat := [371285126407773560, 371285126456177314, 371285126572501420, 371285126575664202, 371285126530038838, 371285126455541165, 371285126423473687, 371285126427454946, 371285126551768962, 371285126677464379]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480807878002508, 362480932234479376⟩, ⟨372567641479467734, 380177222791137914⟩, true⟩

def words02 : List Nat := [371285126802227425, 371285126826510899, 371285126930875598, 371285127036916721, 371285127164903358, 371285127168066815, 371285127149269034, 371285127117071571, 371285127083668269, 371285127062050723]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475647309443728, 362475771694433108⟩, ⟨840347455125687769, 847959620668526793⟩, true⟩

def words03 : List Nat := [371285127093298216, 371285127172144683, 371285127249829422, 371285127252992884, 371285127168311833, 371285127122466956, 371285127136484202, 371285127139647928, 371285127041384967, 371285126941792647]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480586465016353, 362480710878352340⟩, ⟨392660266599080207, 400275001620499951⟩, true⟩

def words04 : List Nat := [371285126859152051, 371285126862639013, 371285126822492300, 371285126812098091, 371285126800734356, 371285126770552952, 371285126594200003, 371285126541186138, 371285126486482995, 371285126487857255]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479749962160477, 362479874404246579⟩, ⟨468495989521586928, 476113330890298582⟩, true⟩

def words05 : List Nat := [371285126441529913, 371285126355233429, 371285126287492108, 371285126290982816, 371285126272071062, 371285126283585243, 371285126286014587, 371285126271789437, 371285126094411337, 371285126040369349]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481235919472172, 362481360389754372⟩, ⟨333796429840287277, 341416327613232347⟩, true⟩

def words06 : List Nat := [371285126003484065, 371285126006685610, 371285125954345384, 371285125898365392, 371285125841085484, 371285125822324795, 371285125791247223, 371285125830823846, 371285125869301376, 371285125872577944]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495220752065631, 362495345251020830⟩, ⟨(-934322475076452170), (-926699977378225006)⟩, true⟩

def words07 : List Nat := [371285125842308294, 371285125855214875, 371285125928749317, 371285125931914368, 371285125843704271, 371285125751875426, 371285125685090918, 371285125688650039, 371285125794663317, 371285125910945421]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475163301807014, 362475287829318613⟩, ⟨884550134384200917, 892175221720988957⟩, true⟩

def words08 : List Nat := [371285126022555657, 371285126025721103, 371285125982343290, 371285125993436943, 371285126008139767, 371285126011305334, 371285125864084080, 371285125702418473, 371285125539408538, 371285125465460647]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362463824673742635, 362463949229742128⟩, ⟨1912956978706589092, 1920584649757072830⟩, true⟩

def words09 : List Nat := [371285125359133411, 371285125360888258, 371285125361565803, 371285125361857938, 371285125209834815, 371285125033644484, 371285124855787380, 371285124800434093, 371285124593631978, 371285124363697554]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk906

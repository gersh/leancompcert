import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk906A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk906B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk906A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk906B

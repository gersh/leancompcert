import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk587A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360608742196541017, 360608764095321206⟩, ⟨(-1569990127211722541), (-1569121677218249097)⟩, true⟩

def state01 : KState := ⟨⟨360590064072056431, 360590085978653740⟩, ⟨(-473542455408846310), (-472673546512314172)⟩, true⟩

def words00 : List Nat := [360582033601937283, 360582033875928682, 360582034346024502, 360582034816344648, 360582035162513628, 360582035291473049, 360582035292215245, 360582035194248499, 360582035096135675, 360582035127083978]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589891452653087, 360589913366970861⟩, ⟨(-463358984375823236), (-462489622172436428)⟩, true⟩

def words01 : List Nat := [360582035555023336, 360582035983105646, 360582036265179390, 360582036377177797, 360582036414689182, 360582036452440842, 360582036694893376, 360582037045592769, 360582037180458248, 360582037315436105]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595791488597544, 360595813410665380⟩, ⟨(-809854248944161990), (-808984431618906870)⟩, true⟩

def words02 : List Nat := [360582037535544559, 360582037900619369, 360582038257213270, 360582038613940908, 360582038717346690, 360582038718166910, 360582038635668889, 360582038739972014, 360582038772791253, 360582039008192770]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595165516250153, 360595187446126642⟩, ⟨(-773073028806411578), (-772202752840622560)⟩, true⟩

def words03 : List Nat := [360582039097681148, 360582039187256177, 360582039566583370, 360582040134165759, 360582040533357802, 360582040932668362, 360582041110767414, 360582041111588164, 360582041330904162, 360582041555644005]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598222198845608, 360598244136440851⟩, ⟨(-952630111337666721), (-951759381933145829)⟩, true⟩

def words04 : List Nat := [360582042069945305, 360582042453679917, 360582042660744952, 360582042867899894, 360582042951756646, 360582043180342338, 360582043494021293, 360582043807845438, 360582043975897757, 360582044252491078]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk587A

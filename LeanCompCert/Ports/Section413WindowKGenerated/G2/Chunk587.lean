import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk587

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

def state06 : KState := ⟨⟨360617624044998008, 360617645990351586⟩, ⟨(-2092734819608441215), (-2091863634363446837)⟩, true⟩

def words05 : List Nat := [360582044368579174, 360582044484899439, 360582044768300867, 360582044900023138, 360582044900779714, 360582044787349706, 360582044849210283, 360582045253043198, 360582045859573560, 360582046466273313]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601223584833338, 360601245538003310⟩, ⟨(-1129025982724598827), (-1128154338149445563)⟩, true⟩

def words06 : List Nat := [360582046927750060, 360582047347514744, 360582048056731085, 360582048766164395, 360582049218753271, 360582049382683600, 360582049383416299, 360582049372370489, 360582049444866115, 360582049772436118]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564007623607919, 360564029584516888⟩, ⟨1058443966746171344, 1059316066181286330⟩, true⟩

def words07 : List Nat := [360582050389264494, 360582051006243465, 360582051375920036, 360582051456960069, 360582051463881759, 360582051471020767, 360582051679131409, 360582051679952444, 360582051599458107, 360582051293706771]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360632698165469691, 360632720134131133⟩, ⟨(-2979572388948600332), (-2978699833785642436)⟩, true⟩

def words08 : List Nat := [360582050987780039, 360582050931096106, 360582051153388349, 360582051375835356, 360582051376592407, 360582051564828448, 360582052065378904, 360582052566163118, 360582053356043755, 360582054218705547]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360596741125764911, 360596763102254725⟩, ⟨(-865462389458360863), (-864589374026853057)⟩, true⟩

def words09 : List Nat := [360582054935724069, 360582055652808002, 360582056274299942, 360582057083626384, 360582057706861435, 360582058330204791, 360582058784144284, 360582058949643987, 360582059200381704, 360582059451397991]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk587

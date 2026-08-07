import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk025

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362144325621181256, 362144325689684416⟩, ⟨827721983514374694, 827722099749766668⟩, true⟩

def state01 : KState := ⟨⟨362490123325113387, 362490123394193384⟩, ⟨(-37266294491178337), (-37266176810713993)⟩, true⟩

def words00 : List Nat := [371275282147045348, 371275253185226005, 371275197700084730, 371275249073017808, 371275271439465826, 371275271439531332, 371275169322452725, 371275171665347757, 371275276311731856, 371275282224615243]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362234086101590561, 362234086171262223⟩, ⟨607653909965329067, 607654029133824063⟩, true⟩

def words01 : List Nat := [371275290625427310, 371275299019575299, 371275369394344858, 371275369394415989, 371275402575863513, 371275442931169754, 371275482715796299, 371275482715861200, 371275314447930175, 371275218722505804]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362122808603886547, 362122808674137259⟩, ⟨889651025534116794, 889651146164867594⟩, true⟩

def words02 : List Nat := [371275183145229009, 371275183145294276, 371275101242047255, 371275008344013423, 371274915519538322, 371274857837202784, 371274723115205840, 371274631853479632, 371274540663903584, 371274449443372385]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362871632937451572, 362871633008291073⟩, ⟨(-1008518989272960792), (-1008518867149507486)⟩, true⟩

def words03 : List Nat := [371274326305717899, 371274342089155683, 371274444907999209, 371274444908065612, 371274422803121254, 371274386312125286, 371274419177345512, 371274421953762915, 371274578336112405, 371274734595402641]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362791191621643548, 362791191693074903⟩, ⟨(-805506117092367682), (-805505993462634844)⟩, true⟩

def words04 : List Nat := [371274838195707318, 371274838195772892, 371274888290064771, 371274989939466007, 371275138232320706, 371275141113776158, 371275145509636631, 371275149902070387, 371275306989681503, 371275430817550546]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489696236821599, 362489696308844540⟩, ⟨(-33473178085243899), (-33473052943925603)⟩, true⟩

def words05 : List Nat := [371275707128130651, 371275983222278595, 371276236160395637, 371276286454570732, 371276343334614102, 371276400170198890, 371276609035905446, 371276615787836035, 371276620897463822, 371276626003126491]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362370862127433241, 362370862200047311⟩, ⟨272986265158187059, 272986391815865477⟩, true⟩

def words06 : List Nat := [371276730456417904, 371276781597180830, 371276904874573624, 371277028055869247, 371277135524048734, 371277135524114796, 371277042418753064, 371277035983343412, 371277082585899505, 371277082585967882]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362542142313601416, 362542142386818188⟩, ⟨(-167557113910154131), (-167556985700467613)⟩, true⟩

def words07 : List Nat := [371277041271203810, 371276999254988029, 371277033041450859, 371277070511843649, 371277145927401889, 371277221284457378, 371277296137635502, 371277296137701806, 371277197818636362, 371277222981277519]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362102418895674597, 362102418969484504⟩, ⟨968827042832629537, 968827172575698947⟩, true⟩

def words08 : List Nat := [371277347900856859, 371277347900923329, 371277275037642224, 371277160268934797, 371277045588997681, 371276932336706221, 371276745354245972, 371276657999406962, 371276570712027910, 371276483514880527]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500810993940799, 362500811068355540⟩, ⟨(-63977366244301390), (-63977234931708816)⟩, true⟩

def words09 : List Nat := [371276341924534449, 371276344702803236, 371276494406529755, 371276494406596605, 371276448050570621, 371276377406259964, 371276306816327978, 371276287444779148, 371276204439459706, 371276213899985026]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk025

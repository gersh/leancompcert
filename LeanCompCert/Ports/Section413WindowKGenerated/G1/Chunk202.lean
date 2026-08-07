import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk202

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362455542080550405, 362455547548336364⟩, ⟨594253547292443915, 594328246238352809⟩, true⟩

def state01 : KState := ⟨⟨362478967453759487, 362478972927164759⟩, ⟨121235742971411233, 121310555456166475⟩, true⟩

def words00 : List Nat := [371284969268911607, 371284969590643457, 371284971910886060, 371284974231147436, 371284976195286737, 371284976195913996, 371284974901733641, 371284974733142244, 371284975428022189, 371284975428671744]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477937778434155, 362477943257549154⟩, ⟨141992369159556565, 142067297067054785⟩, true⟩

def words01 : List Nat := [371284975132149271, 371284974843383475, 371284974877963761, 371284974878661073, 371284973993802562, 371284973535546000, 371284973077105767, 371284972467956288, 371284969682274343, 371284969335544558]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362452793145216010, 362452798629931350⟩, ⟨650558449473213156, 650633490648537992⟩, true⟩

def words02 : List Nat := [371284970796477133, 371284970797104979, 371284969352343821, 371284967400988435, 371284965449578155, 371284964203833285, 371284961736241231, 371284961469138319, 371284961201856238, 371284960443606513]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362517219404208141, 362517224894602506⟩, ⟨(-652973651282933993), (-652898495192443597)⟩, true⟩

def words03 : List Nat := [371284959700065468, 371284960546506259, 371284963827621200, 371284964287506737, 371284964507840268, 371284964728340348, 371284965708535546, 371284965709227327, 371284967063093424, 371284968657499970]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493199753172141, 362493205249236400⟩, ⟨(-166836674008040332), (-166761403129865516)⟩, true⟩

def words04 : List Nat := [371284970225282761, 371284970225911670, 371284970189627805, 371284971192708007, 371284972945694163, 371284972946322899, 371284971891802077, 371284970490063508, 371284970117493355, 371284970524870697]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477335553195592, 362477341054921605⟩, ⟨154515166350967821, 154590551908959497⟩, true⟩

def words05 : List Nat := [371284971148358221, 371284971772023263, 371284972236377311, 371284972237010700, 371284971142154158, 371284970797842579, 371284972119951845, 371284972120591656, 371284971764123928, 371284971388184634]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362518645318808291, 362518650826161701⟩, ⟨(-682450969677655401), (-682375470079367091)⟩, true⟩

def words06 : List Nat := [371284973064179409, 371284974278420290, 371284977204431753, 371284980130416122, 371284982551885517, 371284982552514893, 371284982520906564, 371284983307616646, 371284986520129131, 371284988181492994]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475289470546102, 362475294983647837⟩, ⟨196687287407333253, 196762903552768715⟩, true⟩

def words07 : List Nat := [371284989613907364, 371284991046411706, 371284993057833098, 371284994083872285, 371284995814613356, 371284997545418125, 371284999277170622, 371284999277800405, 371284997774099936, 371284997296446297]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362458623061132749, 362458628579845064⟩, ⟨534766695495642846, 534842425453126832⟩, true⟩

def words08 : List Nat := [371284997872615985, 371284997873245843, 371284995694072873, 371284993521521693, 371284991348945710, 371284989925779803, 371284987989246713, 371284988232243702, 371284988481876974, 371284988482528807]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362506547582280584, 362506553106688514⟩, ⟨(-437929857278245814), (-437854011728487214)⟩, true⟩

def words09 : List Nat := [371284988029674904, 371284988876150528, 371284990174512933, 371284990175143281, 371284988668942410, 371284986254269878, 371284983844013713, 371284983844709636, 371284983942834369, 371284985006017194]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk202

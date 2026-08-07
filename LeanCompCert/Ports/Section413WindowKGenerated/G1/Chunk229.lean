import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk229

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362433417312809909, 362433424415958841⟩, ⟨1161925194343571730, 1162035185171554274⟩, true⟩

def state01 : KState := ⟨⟨362506726500835761, 362506733610406686⟩, ⟨(-517116389785369681), (-517006251860737077)⟩, true⟩

def words00 : List Nat := [371284166095201503, 371284165786875091, 371284165289221541, 371284165774719070, 371284165968979126, 371284165969700298, 371284164633177115, 371284164918324575, 371284166771956236, 371284167757678271]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499386687156424, 362499393803286579⟩, ⟨(-348887459817240442), (-348777171587774476)⟩, true⟩

def words01 : List Nat := [371284168391357984, 371284169025224739, 371284170619271182, 371284171547018091, 371284173050195703, 371284174553511663, 371284176052775828, 371284176053506531, 371284176648308752, 371284177313099076]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479207415956742, 362479214538478037⟩, ⟨113837840814936553, 113948275563174945⟩, true⟩

def words02 : List Nat := [371284179880464183, 371284180249386785, 371284180636832786, 371284181024479707, 371284181462645686, 371284181463437003, 371284181947915825, 371284182943435092, 371284183934837009, 371284183935580662]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487420639036868, 362487427768059520⟩, ⟨(-74500129569045653), (-74389545712913719)⟩, true⟩

def words03 : List Nat := [371284184834671044, 371284185950764007, 371284187772341947, 371284187773060743, 371284187062982367, 371284185793694576, 371284185154697094, 371284185155488817, 371284184979738232, 371284185121892705]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483323666203341, 362483330801722505⟩, ⟨19342300718487779, 19453033637120501⟩, true⟩

def words04 : List Nat := [371284185261129513, 371284185261848651, 371284182871076675, 371284182380507169, 371284181889618830, 371284181720136499, 371284180500940367, 371284179278205429, 371284178427629368, 371284178428460506]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362457693320645818, 362457700462657832⟩, ⟨607844237001857505, 607955118964460621⟩, true⟩

def words05 : List Nat := [371284179873722424, 371284181356086473, 371284182491411440, 371284182492131973, 371284181610051826, 371284181302715561, 371284181647568326, 371284181648291344, 371284180496625991, 371284179344145832]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476947113469657, 362476954261918261⟩, ⟨165922629528883957, 166033659308250861⟩, true⟩

def words06 : List Nat := [371284178934732665, 371284178935525646, 371284180666827632, 371284182480941315, 371284183989411834, 371284183990131794, 371284182973689718, 371284182314797579, 371284182544120851, 371284182544865943]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475864749269091, 362475871904270678⟩, ⟨190963337351044115, 191074517686366111⟩, true⟩

def words07 : List Nat := [371284182230738905, 371284181958858044, 371284183308749264, 371284184235848548, 371284185719805367, 371284187203917239, 371284188404348244, 371284188405068640, 371284187083234271, 371284186722272696]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362441546772797021, 362441553934226885⟩, ⟨979661076327477463, 979772404417568239⟩, true⟩

def words08 : List Nat := [371284186602642834, 371284186603363379, 371284184324436743, 371284181900722838, 371284179476933074, 371284177625608618, 371284174834146672, 371284173695016908, 371284172555737337, 371284171263692634]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490386737543651, 362490393905486113⟩, ⟨(-143353427352361652), (-143241949504773540)⟩, true⟩

def words09 : List Nat := [371284169410529587, 371284169237584943, 371284170781337774, 371284170782058575, 371284169981084089, 371284168787344301, 371284167593425751, 371284167129279942, 371284165993820642, 371284166265405040]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk229

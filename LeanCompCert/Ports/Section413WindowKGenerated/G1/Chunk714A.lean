import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk714A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486740428317188, 362486816202884577⟩, ⟨(-116775513765125941), (-113121673256515179)⟩, true⟩

def state01 : KState := ⟨⟨362473595824907008, 362473671621255569⟩, ⟨821835332190186925, 825490727990314731⟩, true⟩

def words00 : List Nat := [371285232013213132, 371285232015665921, 371285231937981047, 371285231861419295, 371285231783944476, 371285231766772883, 371285231650744156, 371285231600467326, 371285231549342204, 371285231497015131]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502440693408913, 362502516511837739⟩, ⟨(-1238102962966810020), (-1234445990300710726)⟩, true⟩

def words01 : List Nat := [371285231370815981, 371285231407755744, 371285231639319271, 371285231708416028, 371285231730182312, 371285231752710094, 371285231898602733, 371285231947454675, 371285232191128198, 371285232435861476]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490591111800808, 362490666952364060⟩, ⟨(-391800400639303519), (-388141847023189303)⟩, true⟩

def words02 : List Nat := [371285232641631146, 371285232700652484, 371285232822963824, 371285232946595523, 371285233130494511, 371285233132943309, 371285233081867612, 371285233014668127, 371285233072390306, 371285233151254974]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492155333408199, 362492231196030632⟩, ⟨(-503486522386306061), (-499826392969304983)⟩, true⟩

def words03 : List Nat := [371285233395735067, 371285233641226268, 371285233885591112, 371285234002856431, 371285234117406635, 371285234233099474, 371285234543309864, 371285234643402762, 371285234743169729, 371285234843894334]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498643695155411, 362498719579728980⟩, ⟨(-966958843573376088), (-963297145857684294)⟩, true⟩

def words04 : List Nat := [371285235128982304, 371285235343750095, 371285235753128120, 371285236163469782, 371285236514513315, 371285236623696046, 371285236884350038, 371285237146301319, 371285237461783084, 371285237653011962]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk714A

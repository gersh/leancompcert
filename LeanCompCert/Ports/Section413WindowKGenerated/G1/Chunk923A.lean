import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk923A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489999450840039, 362490128614716022⟩, ⟨(-471729164044972227), (-463679860301870739)⟩, true⟩

def state01 : KState := ⟨⟨362481443653916997, 362481572846944164⟩, ⟨318011088771432738, 326063083317312738⟩, true⟩

def words00 : List Nat := [371285105087696827, 371285105090987547, 371285105116076584, 371285105185262979, 371285105288753223, 371285105291980585, 371285105239233455, 371285105179752930, 371285105119025966, 371285105108706891]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479214581475301, 362479343803592729⟩, ⟨523830117136713213, 531884797152399011⟩, true⟩

def words01 : List Nat := [371285105151660524, 371285105234244382, 371285105314333262, 371285105317561305, 371285105252154586, 371285105209527486, 371285105235957535, 371285105239187995, 371285105179452337, 371285105120719597]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484040668093228, 362484169919140608⟩, ⟨78252025063081240, 86309376040998158⟩, true⟩

def words02 : List Nat := [371285105067347792, 371285105070943992, 371285105031797781, 371285105005144004, 371285104977517600, 371285104931701530, 371285104794183954, 371285104732291711, 371285104708072295, 371285104711472906]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484573252325939, 362484702532770464⟩, ⟨29106953696035244, 37167019057122476⟩, true⟩

def words03 : List Nat := [371285104703784057, 371285104697610724, 371285104797743120, 371285104867051592, 371285104955775370, 371285105045779724, 371285105111882663, 371285105115111519, 371285105034946160, 371285105034601276]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477476564922602, 362477605874097029⟩, ⟨684461984193084379, 692524702622979729⟩, true⟩

def words04 : List Nat := [371285105134161966, 371285105137390789, 371285105085267571, 371285105034077734, 371285104981570420, 371285104919954351, 371285104798500250, 371285104795537747, 371285104791538289, 371285104788039888]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk923A

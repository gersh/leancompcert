import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk923

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

def state06 : KState := ⟨⟨362491939668917881, 362492069007369288⟩, ⟨(-651299029876556042), (-643233607573506094)⟩, true⟩

def words05 : List Nat := [371285104709067878, 371285104671490006, 371285104707851955, 371285104711081714, 371285104649123746, 371285104566976749, 371285104515065507, 371285104518720510, 371285104586132523, 371285104665194848]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478046578975043, 362478175946530468⟩, ⟨631895721954161079, 639963832454677031⟩, true⟩

def words06 : List Nat := [371285104729354101, 371285104732583515, 371285104663022713, 371285104689564806, 371285104707060323, 371285104710289872, 371285104571732333, 371285104412999464, 371285104252907418, 371285104211469893]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480754166490722, 362480883563151747⟩, ⟨381797558334766366, 389868357466816890⟩, true⟩

def words07 : List Nat := [371285104165897788, 371285104196676053, 371285104216583827, 371285104219813678, 371285104083414832, 371285103983281681, 371285103894484938, 371285103897768617, 371285103873230109, 371285103831147708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493902762371993, 362494032187909257⟩, ⟨(-832879048875455336), (-824805582004470788)⟩, true⟩

def words08 : List Nat := [371285103859099367, 371285103881539237, 371285104019731746, 371285104159282393, 371285104277961413, 371285104299872446, 371285104437803629, 371285104577372783, 371285104751054346, 371285104851025746]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489360366636136, 362489489821714334⟩, ⟨(-413188157756967330), (-405111961464603156)⟩, true⟩

def words09 : List Nat := [371285104938990213, 371285105028057971, 371285105153455288, 371285105234607684, 371285105325145972, 371285105416884967, 371285105505750408, 371285105508981425, 371285105488975284, 371285105540575985]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk923

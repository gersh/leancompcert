import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk304A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557531079008571, 360557536643753486⟩, ⟨786623478852631784, 786737882929286646⟩, true⟩

def state01 : KState := ⟨⟨360592932353052649, 360592937921611836⟩, ⟨(-289814206184402906), (-289699686134736310)⟩, true⟩

def words00 : List Nat := [360583415328435833, 360583414103241551, 360583413868031353, 360583414289759163, 360583414290131199, 360583413785520209, 360583412790428451, 360583412106339036, 360583411459959947, 360583411773634633]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360554940333467663, 360554945905873376⟩, ⟨865722078391110431, 865836715431937541⟩, true⟩

def words01 : List Nat := [360583411773997896, 360583411491837929, 360583411291172273, 360583412102408514, 360583412102754560, 360583411911815934, 360583411720845904, 360583410990720485, 360583409586508624, 360583408651285340]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611970824619462, 360611976400833374⟩, ⟨(-869436683357141003), (-869321930452127179)⟩, true⟩

def words02 : List Nat := [360583407715984160, 360583407445152599, 360583407445512475, 360583406996235056, 360583406546921773, 360583405890237275, 360583407047058195, 360583408203880262, 360583408476311411, 360583409415507486]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360641975936824684, 360641981516850024⟩, ⟨(-1782688502312045577), (-1782573633405959165)⟩, true⟩

def words03 : List Nat := [360583411430453265, 360583413445384703, 360583415771534803, 360583417022838579, 360583417349972412, 360583417677123300, 360583418170691070, 360583419354621167, 360583421278803632, 360583423202950811]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360628590121070681, 360628595704950460⟩, ⟨(-1375524958583000171), (-1375409972329286469)⟩, true⟩

def words04 : List Nat := [360583424525292382, 360583425223516575, 360583425895245672, 360583426567043405, 360583426965591373, 360583427064142104, 360583427064506517, 360583426434053150, 360583426247261848, 360583427731080003]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk304A

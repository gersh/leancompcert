import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk971A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593356293041498, 360593418634215845⟩, ⟨(-1075583314374627503), (-1071495867555339589)⟩, true⟩

def state01 : KState := ⟨⟨360591458632515526, 360591520987130103⟩, ⟨(-891377001916663722), (-887288249986778462)⟩, true⟩

def words00 : List Nat := [360582383836903986, 360582383838313941, 360582383922782920, 360582384019058036, 360582384087919885, 360582384107657167, 360582384108912833, 360582384075382831, 360582384045431259, 360582384141149867]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579664046272848, 360579726414166371⟩, ⟨254043787325573384, 258133828841745200⟩, true⟩

def words01 : List Nat := [360582384233877574, 360582384326853942, 360582384366414341, 360582384367824242, 360582384337439720, 360582384280444367, 360582384270507343, 360582384324184354, 360582384325461904, 360582384299553951]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580506492479312, 360580568873682984⟩, ⟨172187507055703470, 176278841318076542⟩, true⟩

def words02 : List Nat := [360582384273330813, 360582384260244820, 360582384277751586, 360582384295521902, 360582384296847028, 360582384207984881, 360582384013194351, 360582383924841970, 360582383836061447, 360582383749018288]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575992741870499, 360576055136504576⟩, ⟨610654536915513743, 614747175741432481⟩, true⟩

def words03 : List Nat := [360582383731589381, 360582383661099417, 360582383603395552, 360582383670765408, 360582383710791285, 360582383751053183, 360582383752321462, 360582383727414885, 360582383665926288, 360582383602386205]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570233308824492, 360570295716737547⟩, ⟨1170103710942640325, 1174197639753628163⟩, true⟩

def words04 : List Nat := [360582383538386429, 360582383490868712, 360582383337572573, 360582383131223949, 360582382924649530, 360582382691549070, 360582382541599429, 360582382438586135, 360582382335427763, 360582382156673251]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk971A

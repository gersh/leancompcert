import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk838A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567655836775718, 360567701742197613⟩, ⟨1234389666288925091, 1236987612389485445⟩, true⟩

def state01 : KState := ⟨⟨360581884631441603, 360581930548211519⟩, ⟨41980787425917521, 44579684546475139⟩, true⟩

def words00 : List Nat := [360582462755716203, 360582462678755581, 360582462785928720, 360582462900393627, 360582462901503285, 360582462880010338, 360582462716187224, 360582462643237182, 360582462569930726, 360582462461879894]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360590442111792716, 360590488040029684⟩, ⟨(-675295597168847522), (-672695738938319220)⟩, true⟩

def words01 : List Nat := [360582462456628724, 360582462334507528, 360582462231069231, 360582462340077132, 360582462412978864, 360582462486075138, 360582462487157027, 360582462473373360, 360582462558584526, 360582462655711455]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583265841661936, 360583311781216782⟩, ⟨(-73770186045883435), (-71169379093219401)⟩, true⟩

def words02 : List Nat := [360582462868521552, 360582462939504845, 360582462940576529, 360582462940333569, 360582462939906463, 360582462842058345, 360582462835730504, 360582462857186295, 360582462858258028, 360582462818671981]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581975660930220, 360582021611853448⟩, ⟨34406569543456402, 37008329562686600⟩, true⟩

def words03 : List Nat := [360582462851860880, 360582462885418763, 360582463060746107, 360582463127173412, 360582463128296054, 360582463061986143, 360582462995451947, 360582463031026826, 360582463032017657, 360582463027998042]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600756592906166, 360600802555291154⟩, ⟨(-1540350510405154852), (-1537747789378804986)⟩, true⟩

def words04 : List Nat := [360582463023804927, 360582462948576293, 360582463011982254, 360582463115594157, 360582463151016787, 360582463220643390, 360582463221717599, 360582463204093044, 360582463283911363, 360582463504005197]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk838A

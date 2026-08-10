import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk983A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582945507313735, 360583009459635061⟩, ⟨(-60460706259439890), (-56215848425965284)⟩, true⟩

def state01 : KState := ⟨⟨360584049471015006, 360584113436956073⟩, ⟨(-169067581306057158), (-164821384585445284)⟩, true⟩

def words00 : List Nat := [360582437586296157, 360582437512037379, 360582437389164494, 360582437355086018, 360582437320629482, 360582437260146800, 360582437212970497, 360582437085275831, 360582436957285684, 360582436906511002]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570476814528755, 360570540793911211⟩, ⟨1165319613214907378, 1169567131427505520⟩, true⟩

def words01 : List Nat := [360582436959888982, 360582437013536577, 360582437015162588, 360582437016590805, 360582436915038510, 360582436736964068, 360582436558458902, 360582436483630250, 360582436429404340, 360582436309893997]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588875939545859, 360588939932426195⟩, ⟨(-643694587660449015), (-639445742270437515)⟩, true⟩

def words02 : List Nat := [360582436190061910, 360582436236991308, 360582436404454307, 360582436572188265, 360582436646767837, 360582436648196210, 360582436734788359, 360582436830771461, 360582436872447803, 360582436940060915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583015172952658, 360583079179434237⟩, ⟨(-67359456003586677), (-63109273137117701)⟩, true⟩

def words03 : List Nat := [360582436951061238, 360582436962225417, 360582437055660716, 360582437203252119, 360582437310095388, 360582437417194467, 360582437472258127, 360582437473686674, 360582437432083207, 360582437440249796]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581317218233640, 360581381238182939⟩, ⟨99562770098589413, 103814277446769375⟩, true⟩

def words04 : List Nat := [360582437514168703, 360582437515597298, 360582437486596164, 360582437373308860, 360582437259796793, 360582437061949301, 360582436931154761, 360582436903969999, 360582436876627753, 360582436797689262]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk983A

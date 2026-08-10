import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk790A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580647841941389, 360580688452384381⟩, ⟨118399801892168493, 120566602885401081⟩, true⟩

def state01 : KState := ⟨⟨360585111840719863, 360585152461837081⟩, ⟨(-234236333497455817), (-232068689190668667)⟩, true⟩

def words00 : List Nat := [360582214593513443, 360582214687360087, 360582214945306167, 360582215203461929, 360582215308221227, 360582215309350074, 360582215254680854, 360582215256529339, 360582215257457911, 360582215292465846]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574061099358077, 360574101731233004⟩, ⟨638943114774397516, 641111609101437826⟩, true⟩

def words01 : List Nat := [360582215293481120, 360582215251047484, 360582215208404947, 360582215268111629, 360582215309607086, 360582215351308483, 360582215352314357, 360582215313912538, 360582215115436653, 360582215014061421]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360563049590551022, 360563090233075110⟩, ⟨1509058550392039789, 1511227886269451305⟩, true⟩

def words02 : List Nat := [360582214912303638, 360582214881903473, 360582214691547544, 360582214367727248, 360582214043725445, 360582213646074235, 360582213328179355, 360582213058096766, 360582212787906720, 360582212438392958]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578420088871009, 360578460742051252⟩, ⟨294232668321750936, 296402846408562258⟩, true⟩

def words03 : List Nat := [360582212197347540, 360582212116483337, 360582212035291523, 360582212008537366, 360582211881891178, 360582211599680354, 360582211317276600, 360582211030677887, 360582210824331795, 360582210778063507]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582434884990557, 360582475548920586⟩, ⟨(-23239835274343228), (-21068807472117086)⟩, true⟩

def words04 : List Nat := [360582210731625536, 360582210605318289, 360582210319027385, 360582210192890139, 360582210066435203, 360582209900428700, 360582209710216702, 360582209439437196, 360582209168447816, 360582209027213434]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk790A

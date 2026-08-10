import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk841A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551315850020867, 360551362097515626⟩, ⟨2611446769310778712, 2614073432442224762⟩, true⟩

def state01 : KState := ⟨⟨360584581627347521, 360584627886231001⟩, ⟨(-186397888348625642), (-183770267370684148)⟩, true⟩

def words00 : List Nat := [360582444647242176, 360582444360990056, 360582444155249231, 360582444035710280, 360582443916111476, 360582443661601352, 360582443385224019, 360582443220532181, 360582443055489278, 360582443032081477]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360563392696896593, 360563438967288154⟩, ⟨1595945562272656736, 1598574151252878802⟩, true⟩

def words01 : List Nat := [360582443033158796, 360582442965066673, 360582442896725903, 360582442933919683, 360582442952774988, 360582442971830143, 360582442972912968, 360582442884506199, 360582442688628115, 360582442464093348]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571354760517688, 360571401042274939⟩, ⟨926104868598800517, 928734413718585997⟩, true⟩

def words02 : List Nat := [360582442239162653, 360582442155643063, 360582441930911526, 360582441616305313, 360582441301510832, 360582440950624543, 360582440708983552, 360582440608745503, 360582440508370862, 360582440319746930]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588583505987731, 360588629799165238⟩, ⟨(-523455592371357369), (-520825086411926311)⟩, true⟩

def words03 : List Nat := [360582440199445373, 360582440210730690, 360582440211726868, 360582440149237190, 360582440092830220, 360582439911427518, 360582439729791948, 360582439741330883, 360582439815882221, 360582439890720938]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575020196155473, 360575066500840981⟩, ⟨617744213185457827, 620375687482690381⟩, true⟩

def words04 : List Nat := [360582439894568605, 360582439895776276, 360582439761274300, 360582439765423306, 360582439766433917, 360582439734888766, 360582439562180053, 360582439281056806, 360582438999713369, 360582438760941786]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk841A

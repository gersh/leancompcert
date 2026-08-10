import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk938A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486900483376022, 362487034046233622⟩, ⟨(-184665680423168689), (-176207041600961017)⟩, true⟩

def state01 : KState := ⟨⟨362480615411306588, 362480749003774752⟩, ⟨404858566429641758, 413319982872633552⟩, true⟩

def words00 : List Nat := [371285155548630385, 371285155551914148, 371285155422474568, 371285155377760217, 371285155331457286, 371285155315964530, 371285155208158660, 371285155078151178, 371285154946722136, 371285154930465645]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477539252500579, 362477672874478260⟩, ⟨693509873643662601, 701974058529854651⟩, true⟩

def words01 : List Nat := [371285154952407075, 371285155022622373, 371285155091540569, 371285155094882394, 371285155069173440, 371285155067777520, 371285155140857348, 371285155144142557, 371285155087198356, 371285155011107229]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484168738288022, 362484302389715332⟩, ⟨71482875498595716, 79949823498468328⟩, true⟩

def words02 : List Nat := [371285154933634872, 371285154885412862, 371285154791574227, 371285154770712982, 371285154748810562, 371285154709964365, 371285154537607898, 371285154480604386, 371285154457307870, 371285154460732049]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485530638944206, 362485664320308893⟩, ⟨(-56294905336425402), (-47825148168100100)⟩, true⟩

def words03 : List Nat := [371285154454105920, 371285154448411140, 371285154532387968, 371285154585455757, 371285154641702546, 371285154699136960, 371285154756266046, 371285154759551433, 371285154670520859, 371285154680085877]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475158345046228, 362475292055684167⟩, ⟨917115426215864167, 925587930541583707⟩, true⟩

def words04 : List Nat := [371285154727508640, 371285154730851540, 371285154684081645, 371285154638722063, 371285154592130493, 371285154575433645, 371285154500701827, 371285154502503404, 371285154503209148, 371285154473697397]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk938A

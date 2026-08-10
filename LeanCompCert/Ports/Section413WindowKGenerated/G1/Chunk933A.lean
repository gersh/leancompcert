import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk933A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485289746267987, 362485421834484227⟩, ⟨(-34559028176933356), (-26238342564529842)⟩, true⟩

def state01 : KState := ⟨⟨362485344779784154, 362485476897097026⟩, ⟨(-39698463605814601), (-31375063125075347)⟩, true⟩

def words00 : List Nat := [371285140693187839, 371285140696474877, 371285140675175617, 371285140631082538, 371285140585709672, 371285140576625201, 371285140553899823, 371285140602397797, 371285140648201706, 371285140655248530]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495747417036739, 362495879563892212⟩, ⟨(-1010432330890787353), (-1002106173645692775)⟩, true⟩

def words01 : List Nat := [371285140743595492, 371285140833721679, 371285140951032298, 371285140978478472, 371285140987223554, 371285140996957695, 371285141053200367, 371285141056991284, 371285141174277437, 371285141293045933]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492338998636912, 362492471175003391⟩, ⟨(-692374788539087418), (-684045877180922570)⟩, true⟩

def words02 : List Nat := [371285141411150134, 371285141414418884, 371285141514326882, 371285141624576714, 371285141768239351, 371285141771505419, 371285141762269165, 371285141753716986, 371285141846499597, 371285141928802441]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487437022074447, 362487569227831805⟩, ⟨(-234847728560373434), (-226516073997788736)⟩, true⟩

def words03 : List Nat := [371285142048146483, 371285142168749398, 371285142283418168, 371285142286689201, 371285142277134935, 371285142275203575, 371285142380530912, 371285142411114874, 371285142439581117, 371285142469236999]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362496714028908138, 362496846263889374⟩, ⟨(-1100776330038357299), (-1092441947568443815)⟩, true⟩

def words04 : List Nat := [371285142593701595, 371285142669802725, 371285142847218435, 371285143026006901, 371285143174627859, 371285143221291724, 371285143317077688, 371285143414546716, 371285143615108878, 371285143743856719]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk933A

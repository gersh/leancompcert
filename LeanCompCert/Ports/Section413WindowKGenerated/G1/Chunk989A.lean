import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk989A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500010419323067, 362500159507171300⟩, ⟨(-1474460289040340086), (-1464505443965758900)⟩, true⟩

def state01 : KState := ⟨⟨362487461904746103, 362487611024010826⟩, ⟨(-233415440028124874), (-223457487706359156)⟩, true⟩

def words00 : List Nat := [371285351840847498, 371285351844322495, 371285351857859812, 371285351886365936, 371285351936022641, 371285351939507280, 371285351884556664, 371285351830585681, 371285351819779732, 371285351846692769]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478496321521444, 362478645472076645⟩, ⟨653481434699882005, 663442482124775283⟩, true⟩

def words01 : List Nat := [371285351974144746, 371285352103085058, 371285352230613073, 371285352257754371, 371285352311997528, 371285352367921982, 371285352447646952, 371285352451122388, 371285352394838382, 371285352330973985]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483447814097351, 362483596995776496⟩, ⟨163648079758357251, 173612206120877461⟩, true⟩

def words02 : List Nat := [371285352282865229, 371285352286695674, 371285352255388612, 371285352236156235, 371285352215810590, 371285352179143339, 371285352005158527, 371285351935294692, 371285351891646500, 371285351895262202]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488168211991309, 362488317425317535⟩, ⟨(-303387878606766384), (-293420621237951860)⟩, true⟩

def words03 : List Nat := [371285351880167201, 371285351847407828, 371285351825516631, 371285351829373592, 371285351808232415, 371285351812354259, 371285351815378720, 371285351818917563, 371285351779019268, 371285351813273611]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482150551814632, 362482299796087358⟩, ⟨292040558861556697, 302010878237512205⟩, true⟩

def words04 : List Nat := [371285351935882649, 371285351939359763, 371285351939323145, 371285351933242872, 371285351925839391, 371285351905022676, 371285351873958585, 371285351912085461, 371285351948908428, 371285351952512194]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk989A

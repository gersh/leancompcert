import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk989

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

def state06 : KState := ⟨⟨362490208140777834, 362490357416572705⟩, ⟨(-505269616366751253), (-495296177721132179)⟩, true⟩

def words05 : List Nat := [371285351980523143, 371285352041298877, 371285352202322731, 371285352228337486, 371285352237750316, 371285352248230910, 371285352321735773, 371285352345720929, 371285352398696452, 371285352453226325]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481072183956885, 362481221491087439⟩, ⟨398855808214736552, 408832348004779206⟩, true⟩

def words06 : List Nat := [371285352506246303, 371285352509723399, 371285352442867383, 371285352463498617, 371285352513178809, 371285352516716764, 371285352481742026, 371285352428690859, 371285352374207516, 371285352362543485]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478288798073490, 362478438136531014⟩, ⟨674367288839906250, 684346929217459874⟩, true⟩

def words07 : List Nat := [371285352356444010, 371285352393462401, 371285352409307969, 371285352412797051, 371285352343869868, 371285352292130005, 371285352258062602, 371285352261564153, 371285352194450754, 371285352128541698]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483345737984020, 362483495107534790⟩, ⟨173857652835870657, 183840370981178665⟩, true⟩

def words08 : List Nat := [371285352093305996, 371285352097198641, 371285352176198064, 371285352257136670, 371285352321265572, 371285352324744716, 371285352269375080, 371285352252426251, 371285352264962397, 371285352268571069]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487123214556928, 362487272615873875⟩, ⟨(-200084992195597205), (-190099129364293171)⟩, true⟩

def words09 : List Nat := [371285352252440853, 371285352225513206, 371285352268452482, 371285352306623281, 371285352362542858, 371285352419751765, 371285352475677461, 371285352479155850, 371285352418229633, 371285352442043669]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk989

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk933

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

def state06 : KState := ⟨⟨362485306450907024, 362485438715707537⟩, ⟨(-35794896202910666), (-27457729951864454)⟩, true⟩

def words05 : List Nat := [371285143852859500, 371285143963051918, 371285144129700417, 371285144240562650, 371285144385030095, 371285144530717102, 371285144641583046, 371285144644850101, 371285144605680128, 371285144612924235]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483598886770108, 362483731180680910⟩, ⟨123641197948466658, 131981082084981128⟩, true⟩

def words06 : List Nat := [371285144719580871, 371285144722848007, 371285144676793241, 371285144631476403, 371285144584928663, 371285144566522006, 371285144582661694, 371285144644583050, 371285144705006218, 371285144708388793]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492174630502151, 362492306953948163⟩, ⟨(-677104191497378127), (-668761549512458173)⟩, true⟩

def words07 : List Nat := [371285144795080518, 371285144898571978, 371285145048167221, 371285145051434740, 371285145048434261, 371285145030611765, 371285145104735002, 371285145149843178, 371285145228779764, 371285145309186248]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482593958702384, 362482726311601210⟩, ⟨217545454165567927, 225890846606198365⟩, true⟩

def words08 : List Nat := [371285145374720001, 371285145377987983, 371285145315355740, 371285145344273073, 371285145397944593, 371285145401213506, 371285145318629057, 371285145214839967, 371285145109750499, 371285145102120604]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485847787137787, 362485980169473668⟩, ⟨(-86310885443326801), (-77962743727503629)⟩, true⟩

def words09 : List Nat := [371285145149708287, 371285145224584994, 371285145299090795, 371285145302417386, 371285145294751058, 371285145311083399, 371285145419927034, 371285145435503054, 371285145446883021, 371285145459527014]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk933

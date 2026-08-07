import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk255

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360612742702405483, 360612746558742355⟩, ⟨(-746169742208729889), (-746103220412799749)⟩, true⟩

def state01 : KState := ⟨⟨360583568878678897, 360583572738161266⟩, ⟨(-2190597393171893), (-2123995370998287)⟩, true⟩

def words00 : List Nat := [360583489862563033, 360583490146631680, 360583490146929031, 360583489654361232, 360583489161777878, 360583488333838541, 360583489102673132, 360583489871516351, 360583489871815736, 360583489480140374]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360575926396966335, 360575930259598755⟩, ⟨192845924625359592, 192912607020947524⟩, true⟩

def words01 : List Nat := [360583490521506129, 360583491562887546, 360583493494079674, 360583493895764596, 360583493896080777, 360583492844954307, 360583491793847991, 360583490427295263, 360583489826907156, 360583489531033746]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360557208615799396, 360557212481611815⟩, ⟨670510733745881970, 670577497310722376⟩, true⟩

def words02 : List Nat := [360583489235133328, 360583488065494167, 360583487359232152, 360583487771811200, 360583487779889649, 360583487780223528, 360583486260487629, 360583483782107344, 360583481303862331, 360583478736892298]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360504461579042819, 360504465448000227⟩, ⟨2017470785462047541, 2017537629334675839⟩, true⟩

def words03 : List Nat := [360583477708365877, 360583476813217114, 360583475918103355, 360583474262654675, 360583472124683166, 360583469595596967, 360583467066604434, 360583466067229196, 360583463749441512, 360583460656666425]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575883291783435, 360575887163900130⟩, ⟨192975447789597925, 193042372365227763⟩, true⟩

def words04 : List Nat := [360583457564058343, 360583456000702673, 360583455707371857, 360583454824818506, 360583453942309467, 360583451699346867, 360583448498155844, 360583446278737895, 360583444059396501, 360583442638356695]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360519211073266570, 360519214948568984⟩, ⟨1641102985704481034, 1641169991691197706⟩, true⟩

def words05 : List Nat := [360583442342956431, 360583440929825322, 360583439516743350, 360583437603315080, 360583436452344099, 360583434532982044, 360583432613739017, 360583429511863501, 360583425988980033, 360583423477195401]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360521025495838120, 360521029374288283⟩, ⟨1594683570931336477, 1594750657390690259⟩, true⟩

def words06 : List Nat := [360583420965493642, 360583419980645593, 360583417473069255, 360583414192404135, 360583410911933411, 360583407241699968, 360583404332630909, 360583402286969809, 360583400241434419, 360583397409383735]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591579801119420, 360591583682733452⟩, ⟨(-210100451561394437), (-210033284186598551)⟩, true⟩

def words07 : List Nat := [360583394970646129, 360583391891355464, 360583388812208156, 360583386855306825, 360583384252069842, 360583380234476287, 360583376217132709, 360583373724687913, 360583372842505071, 360583373163825411]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582256024647829, 360582259909447148⟩, ⟨28050083218526281, 28117332089026977⟩, true⟩

def words08 : List Nat := [360583373164123699, 360583372713522927, 360583370742870585, 360583370296383077, 360583369849846214, 360583367932871406, 360583365805577657, 360583362919731963, 360583360034048100, 360583358671935973]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360466786144787138, 360466790032745290⟩, ⟨2983813944049836768, 2983881273770723908⟩, true⟩

def words09 : List Nat := [360583359668778470, 360583360708544708, 360583360819547497, 360583360819882407, 360583359971742921, 360583358735133762, 360583357498522969, 360583355732174378, 360583352447874308, 360583347895001959]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk255

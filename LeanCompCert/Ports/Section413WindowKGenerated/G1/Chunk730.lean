import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk730

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482496986678591, 362482576332295156⟩, ⟨194232710115271357, 198144392251839811⟩, true⟩

def state01 : KState := ⟨⟨362489713229668417, 362489792597768858⟩, ⟨(-332577744103330315), (-328664420533068035)⟩, true⟩

def words00 : List Nat := [371285290711248343, 371285290742120044, 371285290850425467, 371285290959696177, 371285291046192586, 371285291048700498, 371285290907086073, 371285290863543117, 371285290959453119, 371285291023752161]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496707496597202, 362496786887481208⟩, ⟨(-843255625864658354), (-839340638746376330)⟩, true⟩

def words01 : List Nat := [371285291087758346, 371285291152587213, 371285291403849906, 371285291574314475, 371285291759181832, 371285291945022608, 371285292085004276, 371285292087529475, 371285292216657671, 371285292377152038]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483444740707603, 362483524153935445⟩, ⟨125262012860891103, 129178631640673647⟩, true⟩

def words02 : List Nat := [371285292616704935, 371285292654163140, 371285292678196228, 371285292703159958, 371285292743490831, 371285292746280860, 371285292804829858, 371285292918982093, 371285292994712644, 371285292997309958]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511097071247932, 362511176507221769⟩, ⟨(-1894360282458837083), (-1890442002429107615)⟩, true⟩

def words03 : List Nat := [371285293029013811, 371285293086237996, 371285293319597501, 371285293391765857, 371285293430144930, 371285293469269503, 371285293694709931, 371285293864572070, 371285294220636246, 371285294577861149]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494389724916463, 362494469183488271⟩, ⟨(-674000964357814844), (-670081033654310740)⟩, true⟩

def words04 : List Nat := [371285294914296514, 371285295025785196, 371285295323774904, 371285295623057814, 371285295929301674, 371285295986533245, 371285296041456644, 371285296097243493, 371285296271195586, 371285296399629675]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473275861323860, 362473355342497050⟩, ⟨868511178201681423, 872432760052205121⟩, true⟩

def words05 : List Nat := [371285296578823668, 371285296759045302, 371285296937578554, 371285296940087996, 371285296868820647, 371285296842045741, 371285296940605893, 371285296943115440, 371285296822052431, 371285296661413725]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362499989929642724, 362500069433262911⟩, ⟨(-1083303356403203750), (-1079380134459574360)⟩, true⟩

def words06 : List Nat := [371285296523454523, 371285296526268842, 371285296641959418, 371285296795303656, 371285296917017615, 371285296921282500, 371285297081599515, 371285297243184696, 371285297566227073, 371285297770982943]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493354283750612, 362493433810324857⟩, ⟨(-598420732480194117), (-594495833174073095)⟩, true⟩

def words07 : List Nat := [371285297958431069, 371285298146734494, 371285298336546190, 371285298456257358, 371285298604944383, 371285298754563132, 371285298903769550, 371285298906280355, 371285298943487813, 371285299058020236]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479904577969890, 362479984126890826⟩, ⟨384580289843947915, 388506822362741305⟩, true⟩

def words08 : List Nat := [371285299342992276, 371285299379290795, 371285299388937022, 371285299399421599, 371285299453019780, 371285299455799404, 371285299485061479, 371285299533974171, 371285299582252762, 371285299584851734]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505741731090147, 362505821302678760⟩, ⟨(-1503964344307473546), (-1500036154893432796)⟩, true⟩

def words09 : List Nat := [371285299628181889, 371285299745506947, 371285299999453541, 371285300131090186, 371285300209271009, 371285300288240976, 371285300526602801, 371285300687002274, 371285300969433294, 371285301252954496]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk730

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk154

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362441507968687022, 362441511071176305⟩, ⟨654386139426850387, 654418459320079117⟩, true⟩

def state01 : KState := ⟨⟨362481751959155656, 362481755065824979⟩, ⟨34730638269691679, 34763022556836933⟩, true⟩

def words00 : List Nat := [371284004470583084, 371284004471098756, 371284007606981284, 371284010992569131, 371284014093065524, 371284014093533002, 371284011585063744, 371284010360700554, 371284010939614055, 371284010940098622]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362508694117499783, 362508697228422231⟩, ⟨(-380495393387575879), (-380462943537721111)⟩, true⟩

def words01 : List Nat := [371284010794070103, 371284009915951696, 371284012363930786, 371284014163587866, 371284017241191154, 371284020318577767, 371284023286290322, 371284023286760474, 371284023885207364, 371284025485763667]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476567284211600, 362476570399310112⟩, ⟨115111600060537983, 115144114326917661⟩, true⟩

def words02 : List Nat := [371284028787758932, 371284028788230229, 371284028397430857, 371284027586465260, 371284027199668571, 371284027200188688, 371284028050839787, 371284030574732543, 371284032752313887, 371284032752798571]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362522046161613372, 362522049280947478⟩, ⟨(-587022156593340966), (-586989576950313666)⟩, true⟩

def words03 : List Nat := [371284034551328483, 371284036833401176, 371284040108205147, 371284040108673739, 371284037794434863, 371284034441853300, 371284031089519521, 371284031086208402, 371284031820768567, 371284034283411677]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475021770051093, 362475024893619521⟩, ⟨139303974063075912, 139336619105421364⟩, true⟩

def words04 : List Nat := [371284036738100666, 371284036738577497, 371284038944800956, 371284042142308600, 371284046610539713, 371284046611008678, 371284045498894593, 371284044248795604, 371284043444483199, 371284043445017931]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362391138493069995, 362391141620857937⟩, ⟨1436053453778235754, 1436086164033410458⟩, true⟩

def words05 : List Nat := [371284046462018163, 371284050062425199, 371284052934122410, 371284052934591512, 371284050231578667, 371284047744148639, 371284045256784151, 371284044068977148, 371284038066680014, 371284032058376269]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498313534965784, 362498316666960175⟩, ⟨(-221430422109925653), (-221397646801463641)⟩, true⟩

def words06 : List Nat := [371284026050646714, 371284024223479819, 371284020311638748, 371284017832169389, 371284015352871252, 371284012213026786, 371284006473824330, 371284004912514298, 371284005247793841, 371284006173339759]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497412759154263, 362497415895432289⟩, ⟨(-207303973671079589), (-207271132073347321)⟩, true⟩

def words07 : List Nat := [371284007137336909, 371284008101369722, 371284013239005289, 371284016302664113, 371284020617580457, 371284024932113876, 371284027549345052, 371284027549815288, 371284026286826897, 371284027152323101]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362453552919015589, 362453556059483282⟩, ⟨471979072793910153, 472011979269166903⟩, true⟩

def words08 : List Nat := [371284031671619630, 371284031672089873, 371284030636299028, 371284029496372458, 371284028356410231, 371284028039327120, 371284026775544740, 371284027435301924, 371284028104139706, 371284028104626547]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362535069526125676, 362535072670845938⟩, ⟨(-791150724182712252), (-791117751813795398)⟩, true⟩

def words09 : List Nat := [371284026137871221, 371284025861530084, 371284029470612093, 371284029471082881, 371284028616458861, 371284027118358409, 371284028283549356, 371284029521937205, 371284032815365603, 371284036108571647]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk154

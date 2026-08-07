import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk714

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486740428317188, 362486816202884577⟩, ⟨(-116775513765125941), (-113121673256515179)⟩, true⟩

def state01 : KState := ⟨⟨362473595824907008, 362473671621255569⟩, ⟨821835332190186925, 825490727990314731⟩, true⟩

def words00 : List Nat := [371285232013213132, 371285232015665921, 371285231937981047, 371285231861419295, 371285231783944476, 371285231766772883, 371285231650744156, 371285231600467326, 371285231549342204, 371285231497015131]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502440693408913, 362502516511837739⟩, ⟨(-1238102962966810020), (-1234445990300710726)⟩, true⟩

def words01 : List Nat := [371285231370815981, 371285231407755744, 371285231639319271, 371285231708416028, 371285231730182312, 371285231752710094, 371285231898602733, 371285231947454675, 371285232191128198, 371285232435861476]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490591111800808, 362490666952364060⟩, ⟨(-391800400639303519), (-388141847023189303)⟩, true⟩

def words02 : List Nat := [371285232641631146, 371285232700652484, 371285232822963824, 371285232946595523, 371285233130494511, 371285233132943309, 371285233081867612, 371285233014668127, 371285233072390306, 371285233151254974]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492155333408199, 362492231196030632⟩, ⟨(-503486522386306061), (-499826392969304983)⟩, true⟩

def words03 : List Nat := [371285233395735067, 371285233641226268, 371285233885591112, 371285234002856431, 371285234117406635, 371285234233099474, 371285234543309864, 371285234643402762, 371285234743169729, 371285234843894334]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498643695155411, 362498719579728980⟩, ⟨(-966958843573376088), (-963297145857684294)⟩, true⟩

def words04 : List Nat := [371285235128982304, 371285235343750095, 371285235753128120, 371285236163469782, 371285236514513315, 371285236623696046, 371285236884350038, 371285237146301319, 371285237461783084, 371285237653011962]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499527836290536, 362499603743178165⟩, ⟨(-1030106979784413435), (-1026443687617225645)⟩, true⟩

def words05 : List Nat := [371285237823086102, 371285237993938101, 371285238359491383, 371285238628092948, 371285238947167561, 371285239267272609, 371285239586757587, 371285239645954716, 371285239848628944, 371285240052667016]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480937944973343, 362481013873698065⟩, ⟨298403279157980556, 302068131918320174⟩, true⟩

def words06 : List Nat := [371285240335356173, 371285240357947208, 371285240359811725, 371285240335583470, 371285240342731498, 371285240345432256, 371285240319890524, 371285240347914833, 371285240373593042, 371285240376173486]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362509122333120617, 362509198284011674⟩, ⟨(-1716063063032973518), (-1712396625931687864)⟩, true⟩

def words07 : List Nat := [371285240455139865, 371285240594541430, 371285240928204956, 371285241075660357, 371285241188908222, 371285241302891589, 371285241497833205, 371285241640198442, 371285241977012384, 371285242314929937]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490308095386236, 362490384068387663⟩, ⟨(-371134609870839278), (-367466592208329052)⟩, true⟩

def words08 : List Nat := [371285242652250072, 371285242749559186, 371285243041600573, 371285243334933712, 371285243627125306, 371285243699488045, 371285243764611368, 371285243830569003, 371285243953797407, 371285244028491616]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477349104156191, 362477425099236969⟩, ⟨555390062103800167, 559059658329574019⟩, true⟩

def words09 : List Nat := [371285244180761370, 371285244333973008, 371285244486742020, 371285244489193074, 371285244381205532, 371285244328390736, 371285244327442422, 371285244329936339, 371285244222030211, 371285244115437383]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk714

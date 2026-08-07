import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk392

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488744934975914, 362488766704329306⟩, ⟨(-142940505558785065), (-142363842461426329)⟩, true⟩

def state01 : KState := ⟨⟨362475371498960445, 362475393279881353⟩, ⟨381310873203593412, 381887989805605348⟩, true⟩

def words00 : List Nat := [371285135166120247, 371285135167406571, 371285134666589027, 371285134730704434, 371285134991446401, 371285134992729375, 371285134387121571, 371285133653489211, 371285132919353861, 371285132835857013]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463598244138557, 362463620036597449⟩, ⟨843132646538777059, 843710215603928467⟩, true⟩

def words01 : List Nat := [371285132923940166, 371285133260904232, 371285133597666095, 371285133598971500, 371285133396432164, 371285133146271732, 371285133293475113, 371285133294758529, 371285132827834063, 371285132280748493]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486372982938371, 362486394786895730⟩, ⟨(-50226895935749319), (-49648875840808355)⟩, true⟩

def words02 : List Nat := [371285131733151028, 371285131339733979, 371285130621561518, 371285130452177721, 371285130282393158, 371285130011487082, 371285129159480623, 371285128957638033, 371285129201171322, 371285129234759899]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490517767568466, 362490539583245964⟩, ⟨(-212810076363292713), (-212231596429546907)⟩, true⟩

def words03 : List Nat := [371285129262025067, 371285129289730376, 371285129966224638, 371285130401521294, 371285130806190343, 371285131211304359, 371285131400545892, 371285131401832026, 371285131029223470, 371285131168668621]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484051991555087, 362484073818685944⟩, ⟨41051407832715521, 41630337255578079⟩, true⟩

def words04 : List Nat := [371285131956455811, 371285132206288685, 371285132423971667, 371285132642065145, 371285132997189503, 371285133075830782, 371285133583348469, 371285134091384226, 371285134462889840, 371285134464221118]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362511385127877455, 362511406966606771⟩, ⟨(-1031841564864968419), (-1031262180142867269)⟩, true⟩

def words05 : List Nat := [371285135059869837, 371285135683159437, 371285136713305905, 371285137076819746, 371285137333563873, 371285137590730219, 371285138350301004, 371285138791893461, 371285139461854232, 371285140132340123]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487169210283072, 362487191060622195⟩, ⟨(-81134226510263655), (-80554385929034395)⟩, true⟩

def words06 : List Nat := [371285140736599227, 371285140737884566, 371285140643615527, 371285140703057643, 371285140958491709, 371285140959778114, 371285140517852930, 371285140076732561, 371285139763320931, 371285139817060050]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362465714862288241, 362465736724202642⟩, ⟨761611046009538941, 762191341211851493⟩, true⟩

def words07 : List Nat := [371285140427444780, 371285141038332143, 371285141625030385, 371285141626316631, 371285141484853762, 371285141512986242, 371285141765056351, 371285141766343090, 371285141273295178, 371285140780750806]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479020735119452, 362479042608541515⟩, ⟨238934510650649064, 239515257933528842⟩, true⟩

def words08 : List Nat := [371285140287649031, 371285140125578283, 371285139713018778, 371285139788242537, 371285139789248435, 371285139711500488, 371285139014678441, 371285138726108666, 371285138694202352, 371285138695533970]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488874741722358, 362488896626873236⟩, ⟨(-148264897321998052), (-147683689155452094)⟩, true⟩

def words09 : List Nat := [371285138541360327, 371285138261210602, 371285138346473551, 371285138422075017, 371285138616531503, 371285138811487773, 371285139005880957, 371285139007190404, 371285138770607352, 371285138867804626]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk392

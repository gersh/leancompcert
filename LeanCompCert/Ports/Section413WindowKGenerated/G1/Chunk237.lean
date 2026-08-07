import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk237

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502356630490634, 362502364260828135⟩, ⟨(-418544765272075587), (-418422489568362841)⟩, true⟩

def state01 : KState := ⟨⟨362486044994699091, 362486052631674504⟩, ⟨(-31722443553761666), (-31600010496109214)⟩, true⟩

def words00 : List Nat := [371284712332876409, 371284713151144246, 371284713965271692, 371284714779587209, 371284715657511340, 371284715658340190, 371284717165847687, 371284718674661673, 371284719859478014, 371284719916458102]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362551682520234164, 362551690163958908⟩, ⟨(-1588334733469027743), (-1588212140352009185)⟩, true⟩

def words01 : List Nat := [371284721545455435, 371284723174716201, 371284726062622061, 371284726885275586, 371284727347284980, 371284727809491706, 371284729627101446, 371284730672733934, 371284733496153251, 371284736319671062]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494773728608449, 362494781379068410⟩, ⟨(-238303973305181140), (-238181220393939996)⟩, true⟩

def words02 : List Nat := [371284739138995067, 371284740071243148, 371284741723634029, 371284743376261265, 371284745352215371, 371284745352961007, 371284744963101209, 371284744230799185, 371284744242915418, 371284744666734588]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467802661916892, 362467810319083962⟩, ⟨401970908572470661, 402093820677967021⟩, true⟩

def words03 : List Nat := [371284746383036985, 371284748099491075, 371284749844765439, 371284749845511523, 371284749226636229, 371284748918232102, 371284749020666817, 371284749021421577, 371284748429407200, 371284747716753633]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362508287781452298, 362508295445301472⟩, ⟨(-559127763894903406), (-559004693122324766)⟩, true⟩

def words04 : List Nat := [371284748065055175, 371284748250265914, 371284750209571295, 371284752169038568, 371284753853304840, 371284753854051911, 371284755050207472, 371284756535889607, 371284758404815913, 371284759396582584]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362530554326849010, 362530561997526248⟩, ⟨(-1088054215785381380), (-1087930982813079414)⟩, true⟩

def words05 : List Nat := [371284760023939946, 371284760651483626, 371284763052220825, 371284764655473584, 371284766790983195, 371284768926590955, 371284771057316450, 371284771727841259, 371284773655549407, 371284775583536388]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362514683297507580, 362514690974828292⟩, ⟨(-710800149651016824), (-710676758794460952)⟩, true⟩

def words06 : List Nat := [371284779283065695, 371284780782882557, 371284782240006591, 371284783697255791, 371284785075746272, 371284785716034944, 371284788127283097, 371284790538637314, 371284792919415073, 371284794177941562]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362525861124553457, 362525868808631960⟩, ⟨(-976464127628236654), (-976340576104718472)⟩, true⟩

def words07 : List Nat := [371284796336190823, 371284798494647511, 371284802423062131, 371284803994805186, 371284805291261607, 371284806587850179, 371284808663572869, 371284809865522543, 371284811592656009, 371284813319960133]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362534046785783295, 362534054476607258⟩, ⟨(-1171280204495058438), (-1171156492529756318)⟩, true⟩

def words08 : List Nat := [371284815043289726, 371284815690060080, 371284817420580694, 371284819151346436, 371284821243075684, 371284821878342704, 371284822507888883, 371284823137622652, 371284825535333285, 371284827605415221]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494924436537081, 362494932134114530⟩, ⟨(-240248076454502781), (-240124203789688875)⟩, true⟩

def words09 : List Nat := [371284831029756194, 371284834454121642, 371284837233020832, 371284837659212824, 371284838615866202, 371284839572807365, 371284842029009658, 371284842456494020, 371284842880990234, 371284843305754811]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk237

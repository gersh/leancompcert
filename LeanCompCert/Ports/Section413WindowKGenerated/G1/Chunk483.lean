import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk483

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362465534086995681, 362465567702218868⟩, ⟨945243388626446374, 946340332784224334⟩, true⟩

def state01 : KState := ⟨⟨362438048425013933, 362438082054543325⟩, ⟨2272962382519219550, 2274060017742690854⟩, true⟩

def words00 : List Nat := [371285160265227046, 371285160082586724, 371285159329018418, 371285158578463947, 371285157827304988, 371285157209082448, 371285156397501358, 371285155696792607, 371285154995577178, 371285154296682483]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487874989408543, 362487908633497827⟩, ⟨(-134367779504740494), (-133269440822514104)⟩, true⟩

def words01 : List Nat := [371285153323415498, 371285152778092101, 371285152231913807, 371285152113317401, 371285151768354230, 371285151351468899, 371285150933963917, 371285150832218591, 371285150572048272, 371285150630956023]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362459545791250972, 362459579449879510⟩, ⟨1234545113314574750, 1235644154607904180⟩, true⟩

def words02 : List Nat := [371285150632197408, 371285150605829855, 371285150084376517, 371285149691013676, 371285149296892044, 371285149031543675, 371285148257418440, 371285147473871993, 371285146689660866, 371285146264582757]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362451918036883721, 362451951709979156⟩, ⟨1603321372184156168, 1604421112736540816⟩, true⟩

def words03 : List Nat := [371285145736683672, 371285145484659278, 371285145232116914, 371285144981714814, 371285144463573677, 371285143961359715, 371285143458308104, 371285143382399270, 371285142736399254, 371285142051574865]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462239156376348, 362462272843895173⟩, ⟨1104462661615477525, 1105563099468239829⟩, true⟩

def words04 : List Nat := [371285141366079230, 371285141107863719, 371285140694765032, 371285140604885693, 371285140514504258, 371285140309318907, 371285139643339816, 371285139262211307, 371285138880279349, 371285138678423989]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464755535156726, 362464789237359489⟩, ⟨982822843451429927, 983923991344867829⟩, true⟩

def words05 : List Nat := [371285138206714530, 371285137698174579, 371285137188979606, 371285137106790344, 371285136809448360, 371285136611923306, 371285136413849095, 371285136231235213, 371285135478880887, 371285135060174727]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362442387614192790, 362442421330750229⟩, ⟨2064666927238437299, 2065768769399791355⟩, true⟩

def words06 : List Nat := [371285134640560227, 371285134598305161, 371285133986553421, 371285133285230056, 371285132583337612, 371285131905063046, 371285131014852431, 371285130346262656, 371285129677138708, 371285128975352251]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471352632147964, 362471386363228663⟩, ⟨663502530992410391, 664605075717714049⟩, true⟩

def words07 : List Nat := [371285128093526825, 371285127638525738, 371285127182731533, 371285126968266878, 371285126350828088, 371285125668430055, 371285124985411004, 371285124482562954, 371285123831735568, 371285123549580828]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362460008176350228, 362460041921973874⟩, ⟨1212395152181622278, 1213498400565885122⟩, true⟩

def words08 : List Nat := [371285123266847577, 371285122986362769, 371285122267575137, 371285121975462112, 371285121682488475, 371285121521683052, 371285120952438732, 371285120373620640, 371285119794194489, 371285119384271165]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362447489926223272, 362447523686389586⟩, ⟨1818224229308358668, 1819328181484883052⟩, true⟩

def words09 : List Nat := [371285118867158690, 371285118476222370, 371285118084756275, 371285117688317023, 371285116723042883, 371285115890309797, 371285115056793890, 371285114649356416, 371285113886438384, 371285113111626877]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk483

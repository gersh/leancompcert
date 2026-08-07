import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk184

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470156563532238, 362470161063290170⟩, ⟨292721087768786460, 292777089075371746⟩, true⟩

def state01 : KState := ⟨⟨362485844602613794, 362485849107452547⟩, ⟨4059217666680464, 4115312486548238⟩, true⟩

def words00 : List Nat := [371286074087070082, 371286074707425268, 371286075599614315, 371286076491922087, 371286076906139450, 371286076906706991, 371286073389237442, 371286072400316827, 371286072643655134, 371286072644252469]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488773040597645, 362488777550598717⟩, ⟨(-49757084180601436), (-49700894295993634)⟩, true⟩

def words01 : List Nat := [371286072632537638, 371286072197753986, 371286074277815047, 371286075899922036, 371286077993744798, 371286080087563531, 371286081607229332, 371286081607797210, 371286079347172810, 371286079494342489]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362460915267182702, 362460919782242011⟩, ⟨463505314421253927, 463561597504548469⟩, true⟩

def words02 : List Nat := [371286081516653955, 371286081517222113, 371286080135521352, 371286078489608556, 371286076843645197, 371286075213675929, 371286072304622213, 371286072323747786, 371286072337133167, 371286072337722454]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362558256737059489, 362558261257270078⟩, ⟨(-1331089359686732372), (-1331032981639398694)⟩, true⟩

def words03 : List Nat := [371286070973427715, 371286070799030606, 371286073393160990, 371286073410707055, 371286073411147002, 371286072955712602, 371286074536480423, 371286075509636201, 371286079424650952, 371286083339497756]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494683803400101, 362494688328745245⟩, ⟨(-158607211511786940), (-158550738757368056)⟩, true⟩

def words04 : List Nat := [371286087300833007, 371286087345514826, 371286090331054488, 371286093316558054, 371286095998907520, 371286095999477389, 371286095575519973, 371286094609444869, 371286094792114120, 371286095258518300]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362489635597490538, 362489640127958536⟩, ⟨(-65224321383616718), (-65167754085856178)⟩, true⟩

def words05 : List Nat := [371286098662906999, 371286102067162577, 371286105466685306, 371286105467254629, 371286105333350001, 371286105712022107, 371286109026351178, 371286109721441181, 371286109913124519, 371286110104986549]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362534612838398996, 362534617373965103⟩, ⟨(-895425085620102967), (-895368424185280679)⟩, true⟩

def words06 : List Nat := [371286113231813942, 371286115185071057, 371286119394265036, 371286123603241424, 371286127338233571, 371286128661467247, 371286132323196795, 371286135984825348, 371286140468979953, 371286143094056854]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488046758705474, 362488051299476717⟩, ⟨(-35061820541363854), (-35005062942157570)⟩, true⟩

def words07 : List Nat := [371286145573654010, 371286148053179244, 371286150839952985, 371286152167614266, 371286154359916406, 371286156552193572, 371286158717995648, 371286158718565786, 371286157085385097, 371286157188609223]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362445113895911276, 362445118441752143⟩, ⟨758685517016528307, 758742368329208173⟩, true⟩

def words08 : List Nat := [371286160220629105, 371286160221199307, 371286159353394006, 371286158176594533, 371286156999710103, 371286156708017584, 371286155381800414, 371286154831334484, 371286154280731402, 371286153723976546]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362514438207895404, 362514442758885400⟩, ⟨(-523478005135424502), (-523421058589509430)⟩, true⟩

def words09 : List Nat := [371286151505163774, 371286150256176528, 371286150683088015, 371286150683668282, 371286149956168847, 371286148686023067, 371286148534143759, 371286148534771847, 371286149728055563, 371286151257961693]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk184

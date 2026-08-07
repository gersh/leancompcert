import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk756

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485182703036175, 362485268033001970⟩, ⟨(-8775013247381922), (-4418644781550886)⟩, true⟩

def state01 : KState := ⟨⟨362466568474345586, 362466653827464655⟩, ⟨1398559233124878658, 1402917352100345422⟩, true⟩

def words00 : List Nat := [371285209670923975, 371285209673526863, 371285209544177377, 371285209373918799, 371285209202690230, 371285209085692547, 371285208880211734, 371285208746690146, 371285208612276222, 371285208480977423]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 75600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 75600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502126782983169, 362502212159605657⟩, ⟨(-1290174162566360255), (-1285814266377867853)⟩, true⟩

def words01 : List Nat := [371285208237346837, 371285208169824848, 371285208188389165, 371285208191055759, 371285208183950105, 371285208149093992, 371285208250161503, 371285208303171579, 371285208529796548, 371285208757556255]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 75610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 75600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486738344890565, 362486823745018184⟩, ⟨(-126482232592600997), (-122120558826766207)⟩, true⟩

def words02 : List Nat := [371285208958202308, 371285208960805805, 371285209042664038, 371285209160252663, 371285209284558071, 371285209287161628, 371285209178607461, 371285209072651265, 371285209031498968, 371285209055818957]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 75620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 75600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478850637487343, 362478936061085637⟩, ⟨470158459143934992, 474521908114139122⟩, true⟩

def words03 : List Nat := [371285209226185711, 371285209397644178, 371285209545404364, 371285209548020708, 371285209528460251, 371285209518256352, 371285209639272559, 371285209641877139, 371285209566615801, 371285209486629188]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 75630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 75600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479269060492350, 362479354507436137⟩, ⟨438593437472407862, 442958652413211272⟩, true⟩

def words04 : List Nat := [371285209497169075, 371285209528515488, 371285209709465540, 371285209891446932, 371285210033187902, 371285210035792433, 371285209964806704, 371285209919242512, 371285209873564858, 371285209876271738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 75640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 75600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493561619883545, 362493647090528158⟩, ⟨(-642721857264741457), (-638354849236638887)⟩, true⟩

def words05 : List Nat := [371285209800819033, 371285209714508938, 371285209712654527, 371285209716024868, 371285209771412686, 371285209827870543, 371285209883395664, 371285209886023715, 371285209936254728, 371285210050980219]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480830849311313, 362480916343176201⟩, ⟨320550760348105837, 324919525344176201⟩, true⟩

def words06 : List Nat := [371285210293610553, 371285210304306071, 371285210306305948, 371285210283878019, 371285210265117908, 371285210267988595, 371285210215342187, 371285210246301701, 371285210248262290, 371285210244660861]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491937019991197, 362492022537426789⟩, ⟨(-519904309177767050), (-515533760468582778)⟩, true⟩

def words07 : List Nat := [371285210280172062, 371285210373827377, 371285210581417680, 371285210584023315, 371285210575533645, 371285210538434820, 371285210503109121, 371285210505980443, 371285210513292336, 371285210606288610]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494053321814984, 362494138862765617⟩, ⟨(-680129623648798992), (-675757295203858202)⟩, true⟩

def words08 : List Nat := [371285210700184049, 371285210702790097, 371285210642805927, 371285210702316775, 371285210813547532, 371285210816167539, 371285210793743258, 371285210772237366, 371285210899725151, 371285211020681303]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480788605761391, 362480874170179742⟩, ⟨323938846686803362, 328312951523131592⟩, true⟩

def words09 : List Nat := [371285211158235459, 371285211296780331, 371285211423781681, 371285211426388035, 371285211320689454, 371285211269377285, 371285211304406336, 371285211307058264, 371285211251666337, 371285211197280444]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk756

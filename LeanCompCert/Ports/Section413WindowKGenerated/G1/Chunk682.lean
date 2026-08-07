import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk682

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473739038650884, 362473807926291934⟩, ⟨790745669103251768, 793918711098310162⟩, true⟩

def state01 : KState := ⟨⟨362488787924841114, 362488856833371116⟩, ⟨(-235669868954455871), (-232495402229932143)⟩, true⟩

def words00 : List Nat := [371285448794033006, 371285448716162497, 371285448545327925, 371285448561672159, 371285448563475758, 371285448545319055, 371285448271135017, 371285448212982476, 371285448307243196, 371285448359631838]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 68200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 68200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493062638150518, 362493131567881701⟩, ⟨(-527269830081125761), (-524093917114128291)⟩, true⟩

def words01 : List Nat := [371285448375358586, 371285448391813876, 371285448622044437, 371285448745852242, 371285448877493253, 371285449010015427, 371285449141895885, 371285449144230732, 371285449156358358, 371285449271856810]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 68210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 68200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494480173390515, 362494549123926082⟩, ⟨(-623933891267843533), (-620756558920080113)⟩, true⟩

def words02 : List Nat := [371285449522529257, 371285449654786573, 371285449786582738, 371285449919209192, 371285450116915546, 371285450218308843, 371285450533328805, 371285450849268492, 371285451121234897, 371285451256989938]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 68220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 68200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508281160174618, 362508350131811056⟩, ⟨(-1565658400793157924), (-1562479628624633870)⟩, true⟩

def words03 : List Nat := [371285451552965646, 371285451850160300, 371285452256480123, 371285452403908051, 371285452516649927, 371285452630137326, 371285452839197016, 371285452962780389, 371285453299901020, 371285453638081119]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 68230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 68200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491137914095445, 362491206906796580⟩, ⟨(-395789800982456168), (-392609591254407378)⟩, true⟩

def words04 : List Nat := [371285453955932304, 371285454008179427, 371285454149806774, 371285454292605189, 371285454499541238, 371285454501873582, 371285454422859713, 371285454344385387, 371285454382590407, 371285454469597794]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 68240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 68200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362468815661686552, 362468884675348789⟩, ⟨1127897953242455817, 1131079593671342301⟩, true⟩

def words05 : List Nat := [371285454749340439, 371285455030002896, 371285455310073398, 371285455312405898, 371285455306391044, 371285455276162203, 371285455304493617, 371285455306826241, 371285455082420571, 371285454842264572]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484558454940012, 362484627489472918⟩, ⟨53247926147454535, 56430991314653865⟩, true⟩

def words06 : List Nat := [371285454601099602, 371285454575323398, 371285454455072471, 371285454433124658, 371285454410400276, 371285454324553656, 371285454093596760, 371285454021368510, 371285454072546460, 371285454074961635]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490658825485588, 362490727881327482⟩, ⟨(-363267126657691955), (-360082606617763827)⟩, true⟩

def words07 : List Nat := [371285454064628695, 371285454010669866, 371285454080700384, 371285454101175094, 371285454186835729, 371285454273376572, 371285454316717383, 371285454319091450, 371285454260861838, 371285454341007075]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480788316776230, 362480857393394811⟩, ⟨310775206472871802, 313961145252719172⟩, true⟩

def words08 : List Nat := [371285454634096287, 371285454642164910, 371285454649520892, 371285454657626301, 371285454673863874, 371285454676440682, 371285454698557973, 371285454788781255, 371285454859792163, 371285454862208001]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489854371204813, 362489923468908052⟩, ⟨(-308348516480268595), (-305161137721159431)⟩, true⟩

def words09 : List Nat := [371285454908757266, 371285455023882811, 371285455315559782, 371285455322327351, 371285455324135068, 371285455288920172, 371285455402173137, 371285455447029526, 371285455514069005, 371285455582087638]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk682

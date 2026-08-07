import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk416

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489765637774416, 362489790272636090⟩, ⟨(-196126024783075782), (-195433558229072948)⟩, true⟩

def state01 : KState := ⟨⟨362487287709837795, 362487312357046794⟩, ⟨(-93092542238750290), (-92399561973376532)⟩, true⟩

def words00 : List Nat := [371285092474630630, 371285092476009006, 371285092292817046, 371285092491047291, 371285092818505229, 371285092819873523, 371285092466208276, 371285092034398732, 371285091745967101, 371285091800896417]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362461241453218042, 362461266112731641⟩, ⟨990922170085853513, 991615662408190701⟩, true⟩

def words01 : List Nat := [371285092432412615, 371285093064442405, 371285093553657447, 371285093555026051, 371285093275158691, 371285092896496375, 371285092713835842, 371285092715204585, 371285092144086778, 371285091573145101]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488026654705582, 362488051326483932⟩, ⟨(-123890027064797032), (-123196024220846144)⟩, true⟩

def words02 : List Nat := [371285091006132578, 371285091007666404, 371285091120415647, 371285091434890149, 371285091612996850, 371285091614372392, 371285091448855444, 371285091655627413, 371285092016291672, 371285092088795171]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475462706840491, 362475487391106051⟩, ⟨399242709229181226, 399937231979229288⟩, true⟩

def words03 : List Nat := [371285092160639180, 371285092232960790, 371285092572537328, 371285092628289063, 371285092707507206, 371285092787251941, 371285092866305905, 371285092867675529, 371285092260600559, 371285092031643497]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482540170127971, 362482564866609984⟩, ⟨104507692969832216, 105202724475776108⟩, true⟩

def words04 : List Nat := [371285092147669461, 371285092149039531, 371285091838251799, 371285091425024906, 371285091011305074, 371285090771934274, 371285090467524940, 371285090604484906, 371285090740899384, 371285090742347698]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362507351912577018, 362507376621413581⟩, ⟨(-928993580163202350), (-928298034027250712)⟩, true⟩

def words05 : List Nat := [371285091198125138, 371285091715238328, 371285092644038930, 371285092885821526, 371285093039690259, 371285093193990644, 371285093405587666, 371285093407097298, 371285093901836158, 371285094438220013]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490420396347000, 362490445117568372⟩, ⟨(-223615075399607391), (-222919013251509567)⟩, true⟩

def words06 : List Nat := [371285094971190158, 371285094972561214, 371285095201806673, 371285095565396576, 371285096037283997, 371285096038654605, 371285095823406332, 371285095520243854, 371285095487643563, 371285095617598333]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479637127582794, 362479661861168629⟩, ⟨225805927196078640, 226502504634676520⟩, true⟩

def words07 : List Nat := [371285095985735004, 371285096354406887, 371285096687921353, 371285096689292323, 371285096343005888, 371285096176404708, 371285096325450825, 371285096326852103, 371285096311124307, 371285096182297101]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362516544644789306, 362516569390639081⟩, ⟨(-1312640549956293552), (-1311943461293739172)⟩, true⟩

def words08 : List Nat := [371285096497863850, 371285096656610327, 371285097316516482, 371285097976939654, 371285098487439065, 371285098488813318, 371285098899620090, 371285099393824764, 371285100368790492, 371285101125035144]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502124849090836, 362502149607426806⟩, ⟨(-711292983504686684), (-710595374228911824)⟩, true⟩

def words09 : List Nat := [371285101879840059, 371285102635079706, 371285103904418175, 371285104886667926, 371285106009347228, 371285107132515730, 371285108218932282, 371285108539678179, 371285108949286062, 371285109359609514]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk416

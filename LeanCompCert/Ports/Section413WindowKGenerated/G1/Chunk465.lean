import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk465

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482219227128207, 362482250286965495⟩, ⟨146166235263926071, 147142038094371475⟩, true⟩

def state01 : KState := ⟨⟨362459313849880040, 362459344923475856⟩, ⟨1211357011605107494, 1212333454278954656⟩, true⟩

def words00 : List Nat := [371285414599040135, 371285414600583740, 371285414020131158, 371285413439210937, 371285412857712399, 371285412377151500, 371285411699994078, 371285411484981801, 371285411269432941, 371285411005055709]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494925557458683, 362494956645027216⟩, ⟨(-445068433358487929), (-444091340744556841)⟩, true⟩

def words01 : List Nat := [371285410445675374, 371285410348593510, 371285410577075666, 371285410578627081, 371285410465097798, 371285410245272094, 371285410222983856, 371285410224685165, 371285410397777364, 371285410604728329]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479536693944074, 362479567795479981⟩, ⟨270916280279903405, 271894022726966741⟩, true⟩

def words02 : List Nat := [371285410812408119, 371285410813979317, 371285410922260947, 371285411208287581, 371285411631941557, 371285411633486684, 371285411521906834, 371285411407163244, 371285411291798157, 371285411208820342]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362459397681279645, 362459428796696389⟩, ⟨1208156373697968860, 1209134762091932274⟩, true⟩

def words03 : List Nat := [371285411224281795, 371285411365928489, 371285411507609551, 371285411509154667, 371285411108225158, 371285410754216718, 371285410456987964, 371285410458532812, 371285409902471159, 371285409345946324]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476160295796213, 362476191425062310⟩, ⟨427897874636990638, 428876907649763628⟩, true⟩

def words04 : List Nat := [371285408788772712, 371285408470595021, 371285407920751501, 371285407514603018, 371285407107973067, 371285406620814506, 371285405716778322, 371285405217156538, 371285404716755104, 371285404677643401]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472912527370769, 362472943670718867⟩, ⟨579115535207871288, 580095223807862836⟩, true⟩

def words05 : List Nat := [371285404480881902, 371285404244494103, 371285404073447335, 371285404075149813, 371285403911294500, 371285403888678947, 371285403865588407, 371285403753301560, 371285403026239017, 371285402760577284]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465052170095363, 362465083327209873⟩, ⟨945159482004261078, 946139811640163854⟩, true⟩

def words06 : List Nat := [371285402622103348, 371285402623650058, 371285402234795840, 371285401723479448, 371285401211579634, 371285400800998335, 371285400219138588, 371285400098285768, 371285399976906759, 371285399835941679]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500983516004479, 362501014687100116⟩, ⟨(-728347933344512178), (-727366952537156418)⟩, true⟩

def words07 : List Nat := [371285399400761110, 371285399158392377, 371285399131306906, 371285399132864846, 371285399056496736, 371285398870692792, 371285398881280508, 371285398914282449, 371285399250583254, 371285399587541559]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473850418920635, 362473881603946260⟩, ⟨535564303145401204, 536545932884535870⟩, true⟩

def words08 : List Nat := [371285399924512884, 371285399926059261, 371285399728128452, 371285399808857465, 371285399833114764, 371285399834661198, 371285399245446136, 371285398655995055, 371285398065951685, 371285397936482954]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362459659074475885, 362459690273468262⟩, ⟨1196923310495521909, 1197905591013936529⟩, true⟩

def words09 : List Nat := [371285397902992158, 371285398117359277, 371285398324594147, 371285398326140861, 371285397919944406, 371285397654980861, 371285397416128515, 371285397417677630, 371285396951923322, 371285396402030793]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk465

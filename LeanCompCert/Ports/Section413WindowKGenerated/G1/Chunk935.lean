import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk935

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496791808589890, 362496924485523420⟩, ⟨(-1109505185358078237), (-1101129513471018285)⟩, true⟩

def state01 : KState := ⟨⟨362491633608405511, 362491766314859046⟩, ⟨(-627217836049528727), (-618839403889589989)⟩, true⟩

def words00 : List Nat := [371285147952474522, 371285147955746789, 371285148016970761, 371285148107655719, 371285148231461703, 371285148261180730, 371285148287153260, 371285148314201508, 371285148415636380, 371285148490176500]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480800585752395, 362480933321727504⟩, ⟨385844222132462739, 394225415006205253⟩, true⟩

def words01 : List Nat := [371285148621332792, 371285148753833178, 371285148861253537, 371285148864526156, 371285148819314225, 371285148795993738, 371285148815804605, 371285148819089495, 371285148775922765, 371285148734633901]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490996082826490, 362491128848082906⟩, ⟨(-567654621864011499), (-559270690455282855)⟩, true⟩

def words02 : List Nat := [371285148733368218, 371285148753375400, 371285148886332542, 371285149020590569, 371285149134726237, 371285149137999743, 371285149119659574, 371285149132811151, 371285149258565875, 371285149325887535]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489691260529677, 362489824055571682⟩, ⟨(-445597118314820224), (-437210400909824620)⟩, true⟩

def words03 : List Nat := [371285149391924286, 371285149459036821, 371285149582906296, 371285149674171590, 371285149784480764, 371285149896080063, 371285149999766788, 371285150003040719, 371285150004075788, 371285150058063533]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478374611091460, 362478507435328394⟩, ⟨613003495495673551, 621392943946961511⟩, true⟩

def words04 : List Nat := [371285150139034983, 371285150142309066, 371285150071114242, 371285150000752601, 371285149929084552, 371285149884878713, 371285149783932197, 371285149789556664, 371285149793708474, 371285149797102280]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362497024719055598, 362497157572894422⟩, ⟨(-1131823607837980058), (-1123431389980399278)⟩, true⟩

def words05 : List Nat := [371285149729289249, 371285149734216329, 371285149851703127, 371285149854980438, 371285149849217045, 371285149802122888, 371285149817392159, 371285149835052789, 371285149965615454, 371285150097664568]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495498858416609, 362495631741846200⟩, ⟨(-989055141459101479), (-980660154940804447)⟩, true⟩

def words06 : List Nat := [371285150228112401, 371285150278622314, 371285150442305018, 371285150607690473, 371285150806180517, 371285150903535292, 371285150999721222, 371285151097070396, 371285151240568240, 371285151356310716]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489826526726885, 362489959439600724⟩, ⟨(-458210498410708539), (-449812756642790751)⟩, true⟩

def words07 : List Nat := [371285151575534892, 371285151796058779, 371285152004626078, 371285152123333932, 371285152269075264, 371285152416525012, 371285152608276240, 371285152663217121, 371285152717030247, 371285152772043819]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362491175043822623, 362491307986062187⟩, ⟨(-584392153190758731), (-575991663229084345)⟩, true⟩

def words08 : List Nat := [371285152939865673, 371285153052805290, 371285153191873614, 371285153332275289, 371285153439674807, 371285153442950902, 371285153431634656, 371285153452777421, 371285153568001822, 371285153637212094]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489301474269960, 362489434446407019⟩, ⟨(-408996737053729349), (-400593448843328903)⟩, true⟩

def words09 : List Nat := [371285153705947907, 371285153775795581, 371285153948062833, 371285154077162706, 371285154239692889, 371285154403445799, 371285154544037360, 371285154549733634, 371285154597695795, 371285154647592441]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk935

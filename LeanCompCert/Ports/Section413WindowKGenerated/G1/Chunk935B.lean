import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk935A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk935B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk935A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk935B

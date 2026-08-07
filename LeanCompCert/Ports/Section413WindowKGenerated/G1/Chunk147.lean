import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk147

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474753056800848, 362474755872012978⟩, ⟨127802472584533167, 127830468055292287⟩, true⟩

def state01 : KState := ⟨⟨362380431735063360, 362380434554229615⟩, ⟨1514968409977312143, 1514996463594467199⟩, true⟩

def words00 : List Nat := [371283454422494180, 371283454422938240, 371283451465465552, 371283448250190342, 371283445035178583, 371283442112925779, 371283437589931427, 371283433560459584, 371283429531390648, 371283425476295861]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362533348947496892, 362533351770684515⟩, ⟨(-735168678354810451), (-735140565563113739)⟩, true⟩

def words01 : List Nat := [371283418475651641, 371283415291548252, 371283413527708356, 371283413528160258, 371283411133692930, 371283408139832228, 371283406754999720, 371283406762364795, 371283410155670409, 371283413548718405]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362457735913644103, 362457738740848879⟩, ⟨378210184784641866, 378238356729554766⟩, true⟩

def words02 : List Nat := [371283416071034439, 371283416071480285, 371283416409702137, 371283418878558021, 371283422420551854, 371283422420996849, 371283420774896454, 371283419102299487, 371283417429741267, 371283416837028754]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362419777127319552, 362419779958524133⟩, ⟨937895829748389570, 937924060631145730⟩, true⟩

def words03 : List Nat := [371283417946246745, 371283420798387194, 371283423708337926, 371283423708783148, 371283421332072598, 371283419104553167, 371283419242339144, 371283419242784352, 371283415486937274, 371283411170235880]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476015581416571, 362476018416611131⟩, ⟨109030600248862621, 109058889963891961⟩, true⟩

def words04 : List Nat := [371283407128301919, 371283407128807906, 371283408418149366, 371283410673802861, 371283412169348885, 371283412169794397, 371283409191751705, 371283409997000811, 371283412239197969, 371283412239659531]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494110202401859, 362494113041664349⟩, ⟨(-157963931743083879), (-157935582005997509)⟩, true⟩

def words05 : List Nat := [371283411738756173, 371283410112321229, 371283411443824274, 371283412124756342, 371283413403373211, 371283414681990944, 371283415930208811, 371283415930654746, 371283412798420909, 371283413523880595]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362502257027344980, 362502259870586712⟩, ⟨(-278214491192368048), (-278186082701124918)⟩, true⟩

def words06 : List Nat := [371283417641131612, 371283418031188969, 371283418031529267, 371283417182080165, 371283416896146163, 371283416896637961, 371283418891028970, 371283422176146736, 371283425335066381, 371283426610638089]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362560186282128615, 362560189129393591⟩, ⟨(-1134121454834539699), (-1134092986898829371)⟩, true⟩

def words07 : List Nat := [371283432459592898, 371283438307980818, 371283445126112783, 371283446706816007, 371283447751977832, 371283448797140002, 371283451718061944, 371283452340793231, 371283457533030952, 371283462724759343]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362525010911627894, 362525013762926239⟩, ⟨(-614177626009822215), (-614149098441114321)⟩, true⟩

def words08 : List Nat := [371283467833647095, 371283468273347074, 371283473281594483, 371283478289413472, 371283484709748769, 371283485045806796, 371283485339098338, 371283485632492798, 371283489144535742, 371283491952471158]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503038814453819, 362503041669786970⟩, ⟨(-289026445332591710), (-288997858068652528)⟩, true⟩

def words09 : List Nat := [371283496636004378, 371283501319084061, 371283505974970977, 371283506294734705, 371283506717188706, 371283507139803678, 371283512121424536, 371283513467168898, 371283514786976779, 371283516106779832]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk147

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk145

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362370305454282528, 362370308190104675⟩, ⟨1644240441247918862, 1644267277593550504⟩, true⟩

def state01 : KState := ⟨⟨362391143262644962, 362391146002379978⟩, ⟨1342251485273698440, 1342278378375874834⟩, true⟩

def words00 : List Nat := [371283698113690151, 371283693240714926, 371283685996521287, 371283683487258871, 371283680978194733, 371283677650912026, 371283668009139561, 371283662240343529, 371283656472116722, 371283653127009605]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362446389809177495, 362446392552907853⟩, ⟨540213086540742723, 540240037635288453⟩, true⟩

def words01 : List Nat := [371283646752377090, 371283639509034712, 371283632266508487, 371283628367813462, 371283622412215638, 371283617934861977, 371283613457984254, 371283609014112846, 371283601729137022, 371283599167070063]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362392815903192479, 362392818650819643⟩, ⟨1318469354028349028, 1318496361724860172⟩, true⟩

def words02 : List Nat := [371283597214795415, 371283597215233412, 371283592402114713, 371283587303689148, 371283582205808340, 371283577440646197, 371283570407860252, 371283567658697237, 371283564909759912, 371283561690167535]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478178520702919, 362478181272290891⟩, ⟨77833972604281371, 77861037871528643⟩, true⟩

def words03 : List Nat := [371283555445677637, 371283551624200353, 371283548695168286, 371283548695608717, 371283545611056916, 371283541589367020, 371283538258145473, 371283538258628058, 371283536594581335, 371283536226752482]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492577041885439, 362492579797430211⟩, ⟨(-131792599364369887), (-131765476544804027)⟩, true⟩

def words04 : List Nat := [371283535858814915, 371283535020409587, 371283529968293304, 371283529626768004, 371283530414774400, 371283530415220442, 371283527655114856, 371283524784469586, 371283523750431980, 371283524373298207]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465353602884039, 362465356362391448⟩, ⟨264705968558576172, 264733149054156730⟩, true⟩

def words05 : List Nat := [371283529701946434, 371283535030044911, 371283538755122743, 371283538755562395, 371283537667574523, 371283537108442030, 371283540693436238, 371283540693875536, 371283539832522476, 371283538584167146]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362504491548777824, 362504494312210454⟩, ⟨(-305009477853888759), (-304982240186475651)⟩, true⟩

def words06 : List Nat := [371283540789963258, 371283541878192771, 371283547668152085, 371283553457493199, 371283558466570091, 371283558467009219, 371283557865112698, 371283558521715688, 371283562105840171, 371283563542861304]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484519446361365, 362484522213796750⟩, ⟨(-13880051587023301), (-13852755579338869)⟩, true⟩

def words07 : List Nat := [371283565029948666, 371283566516972541, 371283569653662661, 371283571063009624, 371283572641036671, 371283574219017801, 371283575768061229, 371283575768501075, 371283572092842725, 371283572158548185]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362453992295728147, 362453995067086841⟩, ⟨431380714117728932, 431408067347702314⟩, true⟩

def words08 : List Nat := [371283574141572131, 371283574142012473, 371283571149217764, 371283568129711873, 371283565110448808, 371283563553199043, 371283561924022263, 371283562842658390, 371283563816963671, 371283563817419103]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362529375422529488, 362529378197871117⟩, ⟨(-668666307112686764), (-668638895751957808)⟩, true⟩

def words09 : List Nat := [371283564447483274, 371283567103923474, 371283574441625209, 371283575537196451, 371283575537543279, 371283575516150247, 371283577865979856, 371283577875422840, 371283581012732006, 371283584149809207]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk145

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk692

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493276014371559, 362493347017732793⟩, ⟨(-552377528343677381), (-549059133516790183)⟩, true⟩

def state01 : KState := ⟨⟨362477094713375744, 362477165738112196⟩, ⟨567447979030550142, 570767853131895516⟩, true⟩

def words00 : List Nat := [371285412824828859, 371285412827237005, 371285412831179941, 371285412939365251, 371285413110215848, 371285413112582842, 371285413005475401, 371285412853483989, 371285412700539444, 371285412636727019]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467465392749377, 362467536438784493⟩, ⟨1234000273499943091, 1237321621789323207⟩, true⟩

def words01 : List Nat := [371285412578374988, 371285412640148496, 371285412701604862, 371285412703972049, 371285412487328644, 371285412325658888, 371285412162685453, 371285412154556047, 371285411898401836, 371285411642797630]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474215325791805, 362474286393044718⟩, ⟨766740888103459321, 770063705195125457⟩, true⟩

def words02 : List Nat := [371285411386169350, 371285411338841806, 371285411196032693, 371285411052022394, 371285410907261839, 371285410744671220, 371285410303429358, 371285410025898390, 371285409747145096, 371285409659044937]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482899265756115, 362482970354590246⟩, ⟨165519067119371413, 168843378390049091⟩, true⟩

def words03 : List Nat := [371285409500146584, 371285409334818857, 371285409208789605, 371285409211416683, 371285409185139870, 371285409192391021, 371285409194209592, 371285409152319459, 371285408910516537, 371285408878252726]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471959415352748, 362472030525275273⟩, ⟨923060363814223002, 926386135355685612⟩, true⟩

def words04 : List Nat := [371285408942265991, 371285408944634617, 371285408790466624, 371285408637622887, 371285408483864520, 371285408338978447, 371285408089074329, 371285408048315100, 371285408006723735, 371285407942392323]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492291927114248, 362492363058451028⟩, ⟨(-485123520293382839), (-481796265706342817)⟩, true⟩

def words05 : List Nat := [371285407750861845, 371285407610486936, 371285407475437798, 371285407477808451, 371285407251854715, 371285407005230354, 371285406757610367, 371285406719147182, 371285406713540679, 371285406816616427]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477634819733294, 362477705972431009⟩, ⟨530058465164319739, 533387199317593493⟩, true⟩

def words06 : List Nat := [371285406919297786, 371285406921667034, 371285406777916652, 371285406812180230, 371285406853136237, 371285406855506067, 371285406646344299, 371285406396882945, 371285406146486040, 371285406090798522]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470885003358723, 362470956177450579⟩, ⟨997708554594941169, 1001038770827665597⟩, true⟩

def words07 : List Nat := [371285406048642555, 371285406118674320, 371285406180080261, 371285406182455040, 371285406027784424, 371285405883586296, 371285405738193506, 371285405720153165, 371285405557262585, 371285405351394397]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488981003120614, 362489052198414587⟩, ⟨(-256043204180281394), (-252711518956037328)⟩, true⟩

def words08 : List Nat := [371285405144444170, 371285405094884923, 371285404971852596, 371285405005233437, 371285405008420967, 371285405010833372, 371285404872883883, 371285404902645189, 371285405038797876, 371285405093899484]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480168993984150, 362480240210906866⟩, ⟨354603135710947499, 357936319694063617⟩, true⟩

def words09 : List Nat := [371285405148001648, 371285405202871772, 371285405310322753, 371285405314459000, 371285405381260281, 371285405448999806, 371285405516397340, 371285405518767754, 371285405308686413, 371285405237165078]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk692

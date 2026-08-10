import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk692A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk692B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk692A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk692B

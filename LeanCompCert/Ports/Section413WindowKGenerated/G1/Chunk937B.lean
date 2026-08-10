import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk937A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk937B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk937A

def state06 : KState := ⟨⟨362469758467912264, 362469891912487521⟩, ⟨1422858101517946691, 1431305647809507905⟩, true⟩

def words05 : List Nat := [371285158342872989, 371285158368216626, 371285158370709164, 371285158372015807, 371285158220710622, 371285158082172921, 371285157941954775, 371285157863609217, 371285157703477769, 371285157544396753]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479382713325480, 362479516187252855⟩, ⟨520488555179299429, 528938853679381335⟩, true⟩

def words06 : List Nat := [371285157383807706, 371285157338427365, 371285157242459768, 371285157253809261, 371285157256399585, 371285157249245192, 371285157102284437, 371285157043282220, 371285156994920397, 371285156998319075]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473416743586987, 362473550247446547⟩, ⟨1079979303349455716, 1088432408743236828⟩, true⟩

def words07 : List Nat := [371285156940646207, 371285156872867032, 371285156835174238, 371285156838792487, 371285156815855381, 371285156800313591, 371285156783619197, 371285156767518693, 371285156598838247, 371285156479145665]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477456581114433, 362477590114211934⟩, ⟨701123890435851751, 709579737913899561⟩, true⟩

def words08 : List Nat := [371285156357612574, 371285156343765846, 371285156220237879, 371285156094025649, 371285155966520282, 371285155875039066, 371285155758258470, 371285155756500522, 371285155753692397, 371285155736750733]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486900483376022, 362487034046233622⟩, ⟨(-184665680423168689), (-176207041600961017)⟩, true⟩

def words09 : List Nat := [371285155677051090, 371285155699767704, 371285155767962234, 371285155771250609, 371285155716847845, 371285155643849814, 371285155569560527, 371285155554443586, 371285155502554927, 371285155526371351]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk937B

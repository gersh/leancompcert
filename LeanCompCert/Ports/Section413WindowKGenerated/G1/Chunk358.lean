import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk358

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362456133598838667, 362456151620926195⟩, ⟨1033492482452177985, 1033928519334121825⟩, true⟩

def state01 : KState := ⟨⟨362491595300260575, 362491613332764659⟩, ⟨(-236104347555314310), (-235667937708231504)⟩, true⟩

def words00 : List Nat := [371285031499913011, 371285031474251615, 371285031707515352, 371285032214806865, 371285032517069753, 371285032518233844, 371285031781553217, 371285031684099173, 371285032266558214, 371285032451535198]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362468534866687023, 362468552909807558⟩, ⟨589929220907560912, 590366010982447358⟩, true⟩

def words01 : List Nat := [371285032567539832, 371285032683932443, 371285033424195498, 371285033851603460, 371285034357001890, 371285034862830728, 371285035365730373, 371285035366894923, 371285034831674985, 371285034372984065]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362451078003537350, 362451096057026132⟩, ⟨1215383838527834330, 1215821000048076074⟩, true⟩

def words02 : List Nat := [371285034173363583, 371285034174528189, 371285033397312461, 371285032618266271, 371285031838804105, 371285031284837088, 371285030444921487, 371285029998408748, 371285029551541351, 371285029101961887]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511850928373611, 362511868992421871⟩, ⟨(-962438914959876718), (-962001375041726332)⟩, true⟩

def words03 : List Nat := [371285028155722050, 371285027988340401, 371285027974156179, 371285027975325783, 371285027555874794, 371285027016067242, 371285026712757277, 371285026714060999, 371285027434850731, 371285028185105063]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468762394215806, 362468780468756449⟩, ⟨582034710751688912, 582472626771363722⟩, true⟩

def words04 : List Nat := [371285028921482820, 371285028922647998, 371285029017548136, 371285029414216581, 371285029977741478, 371285029978906862, 371285029506051608, 371285028860479394, 371285028214465020, 371285027961832359]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362462347702567672, 362462365787599436⟩, ⟨812188619737080899, 812626911916116603⟩, true⟩

def words05 : List Nat := [371285027833602386, 371285028159012154, 371285028315085860, 371285028316277225, 371285028030039148, 371285027883574212, 371285028142342762, 371285028143508535, 371285027514503685, 371285026883860343]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476999009258111, 362477017104727054⟩, ⟨286732309509101291, 287170976018579991⟩, true⟩

def words06 : List Nat := [371285026252750797, 371285025866293329, 371285025171549416, 371285025213456901, 371285025214367525, 371285025125153287, 371285024114303049, 371285023479702594, 371285022985201156, 371285022986411431]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467036694604462, 362467054800707321⟩, ⟨644137285743160805, 644576333743549771⟩, true⟩

def words07 : List Nat := [371285022764103957, 371285022400772378, 371285022249153904, 371285022250450408, 371285022076565044, 371285021837448182, 371285021597961973, 371285021356823630, 371285020080711297, 371285019581469405]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467763459735085, 362467781576236324⟩, ⟨618181078935206905, 618620500084437885⟩, true⟩

def words08 : List Nat := [371285019252110309, 371285019253305047, 371285018991195394, 371285018734993222, 371285018478369710, 371285018458461791, 371285018130645664, 371285018211325207, 371285018212212679, 371285018146313907]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502001388872868, 362502019515905474⟩, ⟨(-610856600197302399), (-610416801023187429)⟩, true⟩

def words09 : List Nat := [371285017758123374, 371285017850777093, 371285018158121642, 371285018159288840, 371285017537460972, 371285016796095855, 371285016087013931, 371285016088300462, 371285016261093920, 371285016736010118]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk358

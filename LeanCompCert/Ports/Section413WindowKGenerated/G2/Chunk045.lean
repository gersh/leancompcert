import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk045

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360675003137958967, 360675003239292654⟩, ⟨(-435234950799038519), (-435234641134436539)⟩, true⟩

def state01 : KState := ⟨⟨360547199908242882, 360547200010050708⟩, ⟨138586964445533418, 138587276246158310⟩, true⟩

def words00 : List Nat := [360578325142520905, 360578325142571140, 360578296090157033, 360578235597132965, 360578175130956874, 360578081934094086, 360578013749811345, 360577994273217869, 360577974805257501, 360577928896136331]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361079991289666874, 361079991391950324⟩, ⟨(-2268070127432198932), (-2268069813484101792)⟩, true⟩

def words01 : List Nat := [360577926680060637, 360577931273952355, 360577984415517111, 360578019595107748, 360578019595154982, 360578007694139645, 360578032381746202, 360578094995865954, 360578206034932618, 360578317024889032]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361175720255030644, 361175720357796479⟩, ⟨(-2701685687773210003), (-2701685371642345431)⟩, true⟩

def words02 : List Nat := [360578389592258858, 360578492809808289, 360578644385102517, 360578795893416978, 360578933294046667, 360579049620257589, 360579141094763720, 360579232528879943, 360579321820952605, 360579453447259656]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553990429085872, 360553990532329272⟩, ⟨118956181536971670, 118956499833658206⟩, true⟩

def words03 : List Nat := [360579604636932890, 360579755759909747, 360579882138674734, 360579960851522276, 360580026351054914, 360580091821728730, 360580168800891992, 360580198177050479, 360580198177095849, 360580192404539329]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360809754829008020, 360809754932731894⟩, ⟨(-1045118087306111263), (-1045117766825666243)⟩, true⟩

def words04 : List Nat := [360580198399395693, 360580234862108024, 360580240298945797, 360580245733399824, 360580245733447088, 360580207951962706, 360580122774542532, 360580085468887594, 360580058720189031, 360580109191834143]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360716177079428916, 360716177183637994⟩, ⟨(-618978583738336921), (-618978261047851759)⟩, true⟩

def words05 : List Nat := [360580123858656351, 360580138519041348, 360580173933234233, 360580249478068184, 360580312008177831, 360580374510852323, 360580400360826279, 360580406562558563, 360580436336858957, 360580466098119939]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360706789991787157, 360706790096476778⟩, ⟨(-576578650273264534), (-576578325389029228)⟩, true⟩

def words06 : List Nat := [360580543386476331, 360580573558564519, 360580573558610664, 360580573536063292, 360580573513517036, 360580540615518745, 360580570839841835, 360580609663017582, 360580624160890269, 360580651762329102]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360686206959313150, 360686207064486642⟩, ⟨(-483548075115365380), (-483547748017430200)⟩, true⟩

def words07 : List Nat := [360580677428253349, 360580703082967135, 360580741447881990, 360580741447933150, 360580732984617739, 360580682211157755, 360580631459874025, 360580605896447667, 360580628953512877, 360580652000523004]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360433439308507905, 360433439414169937⟩, ⟨674422110156114292, 674422439493959286⟩, true⟩

def words08 : List Nat := [360580652000569076, 360580650844739942, 360580660161648059, 360580688336678156, 360580688336721841, 360580681882454881, 360580628835229255, 360580539479151640, 360580450162008094, 360580372407523741]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360357127623203684, 360357127729350407⟩, ⟨1025613901664091428, 1025614233229140776⟩, true⟩

def words09 : List Nat := [360580355328624380, 360580370247808977, 360580370247854806, 360580361094505677, 360580305470207456, 360580237138710109, 360580168836926767, 360580147346776962, 360580135825237374, 360580087345269786]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk045

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk950A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk950B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk950A

def state06 : KState := ⟨⟨360580240097136216, 360580299748345032⟩, ⟨172629568453889768, 176458553166485046⟩, true⟩

def words05 : List Nat := [360582156590835136, 360582156652421134, 360582156680842352, 360582156682219810, 360582156600459753, 360582156425206315, 360582156249688165, 360582156123237042, 360582156052484455, 360582156034408219]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575862437996181, 360575922102315613⟩, ⟨588780923410083412, 592611154483424010⟩, true⟩

def words06 : List Nat := [360582156016107885, 360582155942365711, 360582155962301264, 360582156028551544, 360582156066308628, 360582156067686256, 360582155995252799, 360582155837973523, 360582155680438861, 360582155521422413]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566369626447403, 360566429303732489⟩, ⟨1491369375164411798, 1495200838947012630⟩, true⟩

def words07 : List Nat := [360582155502024730, 360582155548456348, 360582155549692481, 360582155496367070, 360582155445356679, 360582155366866016, 360582155287955426, 360582155276505638, 360582155181195659, 360582155017225832]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586257297537181, 360586316987847783⟩, ⟨(-399706193340688050), (-395873491029003890)⟩, true⟩

def words08 : List Nat := [360582154852969499, 360582154632018504, 360582154495285917, 360582154469421711, 360582154443453219, 360582154323049736, 360582154092136491, 360582153972244336, 360582153851923287, 360582153886281610]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584084528812118, 360584144232242687⟩, ⟨(-193095447699256794), (-189261497747198208)⟩, true⟩

def words09 : List Nat := [360582153887510023, 360582153865652664, 360582153930874104, 360582154078235890, 360582154115115154, 360582154152182544, 360582154153410104, 360582154134913154, 360582154099251589, 360582154121752291]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk950B

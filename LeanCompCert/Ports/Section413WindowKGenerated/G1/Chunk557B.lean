import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk557A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk557B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk557A

def state06 : KState := ⟨⟨362492358982181541, 362492404304402415⟩, ⟨(-418157120857156777), (-416449934830048351)⟩, true⟩

def words05 : List Nat := [371284934648953630, 371284934819933719, 371284935279344783, 371284935357719944, 371284935359213030, 371284935341562481, 371284935517487861, 371284935552709472, 371284935687936751, 371284935824015944]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478238514125854, 362478283853296523⟩, ⟨369272321810051002, 370980453044757622⟩, true⟩

def words06 : List Nat := [371284935960033419, 371284935961943436, 371284936023925737, 371284936217072470, 371284936474746516, 371284936476623431, 371284936306167671, 371284936110869335, 371284935914821909, 371284935824841167]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362460741757820781, 362460787113861812⟩, ⟨1345236091776810365, 1346945163956866365⟩, true⟩

def words07 : List Nat := [371284935852349392, 371284935999871019, 371284936145719678, 371284936147597009, 371284935907242442, 371284935683308381, 371284935458347143, 371284935434073510, 371284935001908560, 371284934571085851]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362463847519424039, 362463892892277629⟩, ⟨1171963558596392444, 1173673568668638258⟩, true⟩

def words08 : List Nat := [371284934139470669, 371284933871093272, 371284933442978520, 371284933090540192, 371284932737509734, 371284932333313102, 371284931500620442, 371284930989763238, 371284930477973144, 371284930238910873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474607053662095, 362474652443659719⟩, ⟨571656488676864080, 573367455297019514⟩, true⟩

def words09 : List Nat := [371284929863253561, 371284929487355530, 371284929110669519, 371284929055577192, 371284928867175805, 371284928777622911, 371284928687468971, 371284928531482365, 371284928027866183, 371284927846084397]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk557B

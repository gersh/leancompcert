import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk174A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk174B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk174A

def state06 : KState := ⟨⟨360614812926778379, 360614814674620650⟩, ⟨(-538671511502808289), (-538650853513536049)⟩, true⟩

def words05 : List Nat := [360583941723751001, 360583942972126925, 360583946066003695, 360583950788184578, 360583954658187555, 360583958527783191, 360583959664404702, 360583962342808686, 360583964110018515, 360583965877099687]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360596044030858043, 360596045780783878⟩, ⟨(-211116009510872141), (-211095315131940515)⟩, true⟩

def words06 : List Nat := [360583969010922320, 360583969011143802, 360583968894961647, 360583967134626685, 360583965374460309, 360583961354256673, 360583961105974889, 360583962614602096, 360583962614801424, 360583963168733513]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360639503243191656, 360639504995212762⟩, ⟨(-970389697624847047), (-970368966631073403)⟩, true⟩

def words07 : List Nat := [360583967124748095, 360583971080379584, 360583977241466931, 360583980156022500, 360583980244752523, 360583980333490177, 360583983684233624, 360583988720033235, 360583991896205153, 360583995072060135]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360653292073218238, 360653293827349194⟩, ⟨(-1212086386115918803), (-1212065618231475909)⟩, true⟩

def words08 : List Nat := [360583996606841145, 360583996607062854, 360583996449171027, 360583998000406278, 360583998000592809, 360583997670639365, 360583997454808414, 360583994994913867, 360583993334343135, 360583997296663043]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593017622227343, 360593019378449528⟩, ⟨(-157439643058323848), (-157418838587755550)⟩, true⟩

def words09 : List Nat := [360584004516722384, 360584011735998575, 360584016030621436, 360584017085900357, 360584017291685975, 360584017497508871, 360584020959336543, 360584023501762676, 360584024016010801, 360584024530235840]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk174B

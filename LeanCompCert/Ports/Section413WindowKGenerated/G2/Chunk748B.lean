import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk748A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk748B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk748A

def state06 : KState := ⟨⟨360558698063208680, 360558734374529893⟩, ⟨1760770991834345382, 1762606976125860476⟩, true⟩

def words05 : List Nat := [360582282160304205, 360582282012277533, 360582281864147644, 360582281626312083, 360582281335395853, 360582280927646232, 360582280519594965, 360582280289987424, 360582280065674426, 360582279752249982]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598153041254933, 360598189362633577⟩, ⟨(-1193016735198177728), (-1191179997958228774)⟩, true⟩

def words06 : List Nat := [360582279438590156, 360582279303454713, 360582279324252991, 360582279392738266, 360582279393740387, 360582279296102364, 360582279238663227, 360582279228308570, 360582279384263740, 360582279597865400]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583587469459869, 360583623801012112⟩, ⟨(-102361663187795867), (-100524164199847915)⟩, true⟩

def words07 : List Nat := [360582279693499766, 360582279789256313, 360582280062930039, 360582280426790696, 360582280739218784, 360582281051811179, 360582281228593023, 360582281310830521, 360582281329637745, 360582281348798602]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584020207727471, 360584056549312446⟩, ⟨(-134803600879801863), (-132965350590101537)⟩, true⟩

def words08 : List Nat := [360582281503950860, 360582281505016700, 360582281482080883, 360582281360858152, 360582281239467313, 360582281012368419, 360582281006981434, 360582281093976470, 360582281094935471, 360582281097648160]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590302667682310, 360590339019344990⟩, ⟨(-605358658062130913), (-603519653004140717)⟩, true⟩

def words09 : List Nat := [360582281300293185, 360582281503245683, 360582281630763970, 360582281631830004, 360582281581324387, 360582281379082405, 360582281176640927, 360582281237502726, 360582281345951135, 360582281454652875]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk748B

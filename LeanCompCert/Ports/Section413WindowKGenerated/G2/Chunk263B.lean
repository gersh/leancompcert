import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk263A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk263B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk263A

def state06 : KState := ⟨⟨360606374950509687, 360606379083296002⟩, ⟨(-620955929737753704), (-620882238907713852)⟩, true⟩

def words05 : List Nat := [360582830290348262, 360582830355577704, 360582830821143001, 360582830821488558, 360582829852028445, 360582827495039109, 360582825138160498, 360582824234640391, 360582825128503296, 360582826022376170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360553942534445248, 360553946670531609⟩, ⟨761327606482722918, 761401384318070440⟩, true⟩

def words06 : List Nat := [360582826022687404, 360582825983270163, 360582826847718810, 360582827712204422, 360582828205703149, 360582828206048903, 360582827265429482, 360582825003698776, 360582822742078509, 360582820443164073]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360506863645341082, 360506867784684832⟩, ⟨2003161781944937072, 2003235645694178518⟩, true⟩

def words07 : List Nat := [360582819687981327, 360582820027745713, 360582820028054144, 360582819440775605, 360582817420035176, 360582814965951696, 360582812511948219, 360582810468806207, 360582808329673375, 360582805451314635]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360541949350085744, 360541953492701326⟩, ⟨1077216882857357117, 1077290832933676533⟩, true⟩

def words08 : List Nat := [360582802573097012, 360582799531233851, 360582797212857988, 360582794857780584, 360582792502853940, 360582788938026170, 360582784430754005, 360582781356614650, 360582778282605756, 360582775426499495]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552594567507931, 360552598713417579⟩, ⟨796226194862683399, 796300231885982503⟩, true⟩

def words09 : List Nat := [360582773879996029, 360582771475173492, 360582769070467231, 360582768098166255, 360582767963741313, 360582767459431765, 360582766955130968, 360582765317149235, 360582762743168431, 360582761600989018]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk263B

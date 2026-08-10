import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk645A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk645B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk645A

def state06 : KState := ⟨⟨360599579463322300, 360599606153921722⟩, ⟨(-1076260278200731714), (-1075096267556758754)⟩, true⟩

def words05 : List Nat := [360582951225187863, 360582951236305377, 360582951486844418, 360582951942669616, 360582952337843136, 360582952733152617, 360582953004557388, 360582953225868139, 360582953484552787, 360582953743526023]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601302403456966, 360601329102625001⟩, ⟨(-1187622614102642999), (-1186458050225854943)⟩, true⟩

def words06 : List Nat := [360582953921126889, 360582953993638860, 360582953994448528, 360582953946583949, 360582953898573119, 360582953734952049, 360582953978273739, 360582954221777712, 360582954344821419, 360582954630335183]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360628176118264082, 360628202826000028⟩, ⟨(-2923089105915195718), (-2921923988766312858)⟩, true⟩

def words07 : List Nat := [360582954986321531, 360582955342559914, 360582955842406467, 360582956162865251, 360582956239547062, 360582956316273414, 360582956632229965, 360582957094462117, 360582957795812264, 360582958497346612]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605465202112658, 360605491918521266⟩, ⟨(-1456398389565159208), (-1455232712293915650)⟩, true⟩

def words08 : List Nat := [360582958996007860, 360582959504077833, 360582959985416311, 360582960467020311, 360582960888032268, 360582961159654835, 360582961310939251, 360582961462318317, 360582961607648659, 360582961957500475]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360573658087792721, 360573684812763955⟩, ⟨598287019942934006, 599453250317211438⟩, true⟩

def words09 : List Nat := [360582962546341149, 360582963135343811, 360582963604176861, 360582963834391989, 360582964004191467, 360582964174243932, 360582964414747152, 360582964416733195, 360582964417543475, 360582964274843169]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk645B

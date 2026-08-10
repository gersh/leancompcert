import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk553A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk553B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk553A

def state06 : KState := ⟨⟨362491163055484339, 362491207703999718⟩, ⟨(-348741598176450761), (-347071843454515705)⟩, true⟩

def words05 : List Nat := [371284936263519825, 371284936678717657, 371284937093735746, 371284937196373863, 371284937397924071, 371284937600404994, 371284938110312284, 371284938225891545, 371284938340546524, 371284938455910730]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 55350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 55300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491798131090499, 362491842796301914⟩, ⟨(-383915783118616818), (-382245104018360194)⟩, true⟩

def words06 : List Nat := [371284938712175363, 371284938805841864, 371284938935263007, 371284939065388937, 371284939143005568, 371284939144874670, 371284939023248501, 371284939072749280, 371284939324878974, 371284939451518213]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 55360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 55300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498186052804605, 362498230734958575⟩, ⟨(-737604666257969650), (-735933048962241722)⟩, true⟩

def words07 : List Nat := [371284939578050455, 371284939705189710, 371284940157356781, 371284940494826899, 371284940933301762, 371284941372496325, 371284941755148750, 371284941757012169, 371284941945211621, 371284942187461018]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 55370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 55300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489893420232267, 362489938118980202⟩, ⟨(-278290990115604948), (-276618453761617586)⟩, true⟩

def words08 : List Nat := [371284942754334431, 371284942887616956, 371284943020950894, 371284943154964216, 371284943295176791, 371284943305751238, 371284943580941160, 371284943856862177, 371284944102718760, 371284944194809099]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 55380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 55300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505925973688736, 362505970689324783⟩, ⟨(-1166481219211323254), (-1164807747339207928)⟩, true⟩

def words09 : List Nat := [371284944362767381, 371284944531689259, 371284944916973437, 371284944918837602, 371284944870325703, 371284944769782940, 371284944839605577, 371284944895818260, 371284945276610068, 371284945658236189]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 55390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 55300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 55300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk553B

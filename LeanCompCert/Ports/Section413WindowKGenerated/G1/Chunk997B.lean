import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk997A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk997B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk997A

def state06 : KState := ⟨⟨362471752759366520, 362471904552068564⟩, ⟨1332100379837468672, 1342323900072701886⟩, true⟩

def words05 : List Nat := [371285360331486602, 371285360408468117, 371285360474352127, 371285360477859425, 371285360409630050, 371285360369587530, 371285360327754954, 371285360328528316, 371285360215233278, 371285360084346759]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483943750696528, 362484095574780804⟩, ⟨115900215522779502, 126126866611559802⟩, true⟩

def words06 : List Nat := [371285359951847185, 371285359921368654, 371285359864242509, 371285359880902803, 371285359883644880, 371285359884169678, 371285359762158473, 371285359742501975, 371285359747395924, 371285359751052345]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486785610400830, 362486937466434472⟩, ⟨(-167661198183849079), (-157431359341678117)⟩, true⟩

def words07 : List Nat := [371285359741049074, 371285359712480720, 371285359713874302, 371285359717782563, 371285359715357423, 371285359725358249, 371285359733521651, 371285359737091109, 371285359677407008, 371285359697527149]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476851898378733, 362477003785626550⟩, ⟨823562025088018788, 833794978644727148⟩, true⟩

def words08 : List Nat := [371285359756285415, 371285359759793763, 371285359684920649, 371285359611258911, 371285359536265678, 371285359468728939, 371285359349569726, 371285359332302832, 371285359313861635, 371285359281955288]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487917762665841, 362488069681722362⟩, ⟨(-280727108507500885), (-270490980611049815)⟩, true⟩

def words09 : List Nat := [371285359206310221, 371285359216412015, 371285359324947940, 371285359328458355, 371285359320178233, 371285359297359963, 371285359318550674, 371285359322418037, 371285359347275454, 371285359378412666]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk997B

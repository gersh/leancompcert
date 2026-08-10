import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk977A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk977B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk977A

def state06 : KState := ⟨⟨362485295822176414, 362485441363630094⟩, ⟨(-18653790011393375), (-9047666251057891)⟩, true⟩

def words05 : List Nat := [371285349092738988, 371285349069848658, 371285349106628157, 371285349110061795, 371285349053318034, 371285348979137286, 371285348903607418, 371285348883172607, 371285348809926459, 371285348814799262]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474832695106765, 362474978267520855⟩, ⟨1004274732223112127, 1013883882835447419⟩, true⟩

def words06 : List Nat := [371285348818111718, 371285348821603633, 371285348737669170, 371285348741755472, 371285348775850778, 371285348779282871, 371285348674116330, 371285348555178844, 371285348434830121, 371285348359398072]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473942536062593, 362474088139369270⟩, ⟨1091366358356320402, 1100978529492121902⟩, true⟩

def words07 : List Nat := [371285348255660070, 371285348257939576, 371285348259106588, 371285348254840500, 371285348164225240, 371285348107440525, 371285348092302224, 371285348095734794, 371285348002484434, 371285347891153808]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487703471801866, 362487849105860244⟩, ⟨(-254259445473640479), (-244644267280698011)⟩, true⟩

def words08 : List Nat := [371285347778328475, 371285347763258149, 371285347699613216, 371285347667286714, 371285347633877329, 371285347578606599, 371285347422304492, 371285347372369339, 371285347371292844, 371285347400516392]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484519790233311, 362484665455576778⟩, ⟨57106395446204757, 66724633164674155⟩, true⟩

def words09 : List Nat := [371285347419054161, 371285347438800242, 371285347534000587, 371285347578595863, 371285347653428074, 371285347729549175, 371285347784290781, 371285347787724562, 371285347714224392, 371285347711539607]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk977B

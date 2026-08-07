import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk977

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489817327574410, 362489962683545163⟩, ⟨(-460262174862779754), (-450674178357563786)⟩, true⟩

def state01 : KState := ⟨⟨362489856920607892, 362490002307516770⟩, ⟨(-464165909980285204), (-454574890663329798)⟩, true⟩

def words00 : List Nat := [371285349937538960, 371285349940992320, 371285349918161926, 371285349949803419, 371285350011343595, 371285350014834586, 371285349990714123, 371285349967523491, 371285350017341135, 371285350068867454]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477743526410177, 362477888944268458⟩, ⟨719541820684887078, 729135864223668578⟩, true⟩

def words01 : List Nat := [371285350223603084, 371285350379780809, 371285350498575268, 371285350502005563, 371285350489153934, 371285350501446602, 371285350567225714, 371285350570656208, 371285350497066337, 371285350424663707]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482579657615135, 362482725106168556⟩, ⟨246951514479492024, 256548557703311468⟩, true⟩

def words02 : List Nat := [371285350350645885, 371285350347080436, 371285350335515719, 371285350379454262, 371285350405266979, 371285350408697774, 371285350305447654, 371285350229837071, 371285350177387931, 371285350180942969]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481692387534666, 362481837867335510⟩, ⟨333683399405861895, 343283496595357353⟩, true⟩

def words03 : List Nat := [371285350156670927, 371285350133622525, 371285350148606243, 371285350164961255, 371285350184994916, 371285350206365902, 371285350226328941, 371285350229760254, 371285350109946469, 371285350078268551]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473292779311383, 362473438289721866⟩, ⟨1154689589151448830, 1164292678284206976⟩, true⟩

def words04 : List Nat := [371285350052145088, 371285350055576477, 371285349926060475, 371285349800087267, 371285349672754586, 371285349577073403, 371285349442740559, 371285349366318727, 371285349288729592, 371285349212261858]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk977

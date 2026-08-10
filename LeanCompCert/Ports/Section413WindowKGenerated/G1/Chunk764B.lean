import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk764A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk764B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk764A

def state06 : KState := ⟨⟨362498432039907599, 362498519398347806⟩, ⟨(-1022661671817938810), (-1018151076442557954)⟩, true⟩

def words05 : List Nat := [371285202975663199, 371285202967323906, 371285203059749238, 371285203062430986, 371285203047382677, 371285203007720447, 371285203070988417, 371285203092386362, 371285203268333702, 371285203445424845]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489693641393299, 362489781023650702⟩, ⟨(-354544006726647300), (-350031590169979346)⟩, true⟩

def words06 : List Nat := [371285203562385487, 371285203565020505, 371285203511849069, 371285203573031892, 371285203657701926, 371285203660356946, 371285203627585402, 371285203587397750, 371285203649255037, 371285203712118619]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475941634070834, 362476029040067083⟩, ⟨697208745419612047, 701722977404799793⟩, true⟩

def words07 : List Nat := [371285203944607671, 371285204178206922, 371285204402532129, 371285204405167634, 371285204401592226, 371285204388231041, 371285204500932010, 371285204503567607, 371285204405173317, 371285204288202607]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478441253251021, 362478528682847580⟩, ⟨506080828619777925, 510596865680164647⟩, true⟩

def words08 : List Nat := [371285204220850086, 371285204223832609, 371285204242871829, 371285204273688869, 371285204276301525, 371285204278937484, 371285204071553051, 371285204036343599, 371285204021544920, 371285204024273651]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488754895366680, 362488842348999005⟩, ⟨(-282841323362190815), (-278323447690324027)⟩, true⟩

def words09 : List Nat := [371285203938994584, 371285203856377008, 371285203857995181, 371285203902185678, 371285203997438365, 371285204093783666, 371285204179058756, 371285204181699008, 371285204130717412, 371285204181554262]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk764B

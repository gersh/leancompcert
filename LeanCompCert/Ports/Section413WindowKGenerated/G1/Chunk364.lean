import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk364

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362464482188351525, 362464500845144125⟩, ⟨744323577695492851, 744782528067103349⟩, true⟩

def state01 : KState := ⟨⟨362479661661921749, 362479680329306094⟩, ⟨191797456235052468, 192256792200717554⟩, true⟩

def words00 : List Nat := [371284961429565556, 371284961430870825, 371284961464981760, 371284961787925034, 371284961979573501, 371284961980758914, 371284961282925585, 371284960895375657, 371284960657436617, 371284960658671673]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487179325032180, 362487198003198375⟩, ⟨(-81935476532340864), (-81475747944342034)⟩, true⟩

def words01 : List Nat := [371284960514538114, 371284960325023166, 371284960448934505, 371284960528240792, 371284960835613627, 371284961143439798, 371284961436710592, 371284961437896387, 371284960886205161, 371284960949082773]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362453073815195323, 362453092503932563⟩, ⟨1160296604842599547, 1160756718483099955⟩, true⟩

def words02 : List Nat := [371284961032402355, 371284961033588238, 371284960113025468, 371284959157425626, 371284958201415034, 371284957411865681, 371284956343378075, 371284955951040012, 371284955558312239, 371284955164335613]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483210860673790, 362483229560142670⟩, ⟨62258319456576618, 62718824104203740⟩, true⟩

def words03 : List Nat := [371284954290539877, 371284953893188916, 371284953848795950, 371284953849982193, 371284953201243266, 371284952344042932, 371284951486418638, 371284951310617811, 371284950759274705, 371284950713383730]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362447096816846313, 362447115527040745⟩, ⟨1378461519476463948, 1378922415017619770⟩, true⟩

def words04 : List Nat := [371284950667047825, 371284950623426027, 371284950109900171, 371284949976821573, 371284949856499553, 371284949857686319, 371284948869381837, 371284947880083019, 371284946890350654, 371284946045971270]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362442035075031212, 362442053795898401⟩, ⟨1563121954443746146, 1563583239061323596⟩, true⟩

def words05 : List Nat := [371284945008930974, 371284944723920685, 371284944438531304, 371284944091056647, 371284943073978003, 371284942146819106, 371284941219061102, 371284941043112970, 371284939864931389, 371284938690003210]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362457223133797249, 362457241865305560⟩, ⟨1009273811495175566, 1009735484141820128⟩, true⟩

def words06 : List Nat := [371284937514625359, 371284936813505598, 371284935767228398, 371284935032745682, 371284934297930864, 371284933360250662, 371284931420738419, 371284930232862795, 371284929044438509, 371284928607398838]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482466186972169, 362482484929309720⟩, ⟨88531609398187978, 88993677039965572⟩, true⟩

def words07 : List Nat := [371284927849142844, 371284927089671662, 371284926329748946, 371284926321070635, 371284925937796735, 371284925777960523, 371284925617759361, 371284925330953822, 371284924514349091, 371284924448965421]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479789872454574, 362479808625366475⟩, ⟨186285217363835669, 186747670813476529⟩, true⟩

def words08 : List Nat := [371284925034695581, 371284925141369296, 371284925246081270, 371284925351199509, 371284925683485991, 371284925684806644, 371284925894098885, 371284926148400188, 371284926400809464, 371284926402039906]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362508089671598735, 362508108435255494⟩, ⟨(-846550145375111833), (-846087299790678399)⟩, true⟩

def words09 : List Nat := [371284926288980509, 371284926316750753, 371284927093802450, 371284927094991179, 371284926980044309, 371284926736406379, 371284926997155785, 371284927324053475, 371284927959963282, 371284928596352706]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk364

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk441

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360578456498282205, 360578468573679865⟩, ⟨210271735091160202, 210631607893800910⟩, true⟩

def state01 : KState := ⟨⟨360568960920906565, 360568973001972777⟩, ⟨629048092968137937, 629408215783107559⟩, true⟩

def words00 : List Nat := [360583245098222808, 360583245098825344, 360583244992117248, 360583244576566248, 360583244160935485, 360583243614131670, 360583243325568897, 360583243023828511, 360583242722044008, 360583242061500846]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360646529616837575, 360646541703587935⟩, ⟨(-2792940608337698536), (-2792580234767383554)⟩, true⟩

def words01 : List Nat := [360583241928527523, 360583242119202961, 360583242608574002, 360583243289832803, 360583243471227934, 360583243652660756, 360583244236153941, 360583245158249237, 360583246593381787, 360583248028585842]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360642571986314467, 360642584078810746⟩, ⟨(-2618512544798241124), (-2618151917688802662)⟩, true⟩

def words02 : List Nat := [360583248979195614, 360583249780277230, 360583251094384673, 360583252408609257, 360583253572329664, 360583254223961917, 360583254616034951, 360583255008161507, 360583255913208585, 360583257258260820]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583033730955472, 360583045829129654⟩, ⟨9336037520727836, 9696915224569784⟩, true⟩

def words03 : List Nat := [360583259116093143, 360583260973962540, 360583262534633415, 360583263583276178, 360583264162806567, 360583264742465377, 360583265264547100, 360583265518382921, 360583265518920250, 360583265514567456]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586671082552329, 360586683186428961⟩, ⟨(-151118941403224748), (-150757811965737642)⟩, true⟩

def words04 : List Nat := [360583265797351545, 360583266477358019, 360583267234724531, 360583267992169514, 360583268328085487, 360583268328688782, 360583268362226842, 360583268572373356, 360583268572871164, 360583268590792040]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360589474479676254, 360589486589294848⟩, ⟨(-274892345661651249), (-274530962687857589)⟩, true⟩

def words05 : List Nat := [360583268591329459, 360583268411332556, 360583268412488916, 360583269010234583, 360583269477062105, 360583269943978690, 360583270084522736, 360583270085126172, 360583269854849470, 360583269996312628]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571563955352854, 360571576070661186⟩, ⟨515966426365112074, 516328060626236212⟩, true⟩

def words06 : List Nat := [360583270099211426, 360583270099815003, 360583269860606106, 360583269226657609, 360583268592642755, 360583267599980379, 360583266968083683, 360583266609634216, 360583266251135090, 360583265635085598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360623237906109687, 360623250027113395⟩, ⟨(-1766744305882020430), (-1766382420028486426)⟩, true⟩

def words07 : List Nat := [360583265618333759, 360583265866397776, 360583266502229066, 360583266988563366, 360583267074226907, 360583267159935532, 360583267232827454, 360583267626669698, 360583268532146423, 360583269437719120]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579978462680040, 360579990589436552⟩, ⟨144429577059083714, 144791717100122822⟩, true⟩

def words08 : List Nat := [360583270084305068, 360583270219875074, 360583270284831128, 360583270349970638, 360583270350475876, 360583270285008076, 360583269708482008, 360583268688896125, 360583267669240783, 360583267161446060]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569165427526954, 360569177559979834⟩, ⟨622215682126216659, 622578073917619275⟩, true⟩

def words09 : List Nat := [360583267087797184, 360583266870639676, 360583266653426066, 360583266178945242, 360583265487721157, 360583264666322971, 360583263844784432, 360583263419971426, 360583263354818028, 360583263036765301]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk441

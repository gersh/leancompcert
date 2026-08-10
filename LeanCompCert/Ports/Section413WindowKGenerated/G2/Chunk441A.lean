import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk441A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk441A

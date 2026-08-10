import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk958A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579445153479886, 360579505773382441⟩, ⟨256875642990499640, 260797070563363998⟩, true⟩

def state01 : KState := ⟨⟨360606181411509967, 360606242044537838⟩, ⟨(-2304556438497754487), (-2300633753454722209)⟩, true⟩

def words00 : List Nat := [360582228134302125, 360582228300919267, 360582228576098930, 360582228851539854, 360582229033463626, 360582229106835788, 360582229266501137, 360582229426571356, 360582229583491403, 360582229835569612]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612199480932815, 360612260127176336⟩, ⟨(-2881186610521955147), (-2877262659221341529)⟩, true⟩

def words01 : List Nat := [360582230032124286, 360582230228830433, 360582230534240010, 360582230895256608, 360582231228092219, 360582231561173573, 360582231817140653, 360582232022952001, 360582232337455088, 360582232652413797]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603725766491088, 360603786425835799⟩, ⟨(-2069280925970425631), (-2065355719249709275)⟩, true⟩

def words02 : List Nat := [360582232954748522, 360582233148730244, 360582233254291015, 360582233359961001, 360582233437969724, 360582233570591108, 360582233784248062, 360582233998166985, 360582234136786774, 360582234363149928]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360612621451492683, 360612682123945385⟩, ⟨(-2921816430074284832), (-2917889967149478436)⟩, true⟩

def words03 : List Nat := [360582234666377340, 360582234970031440, 360582235347468154, 360582235616584532, 360582235793745008, 360582235971019812, 360582236145291184, 360582236374170793, 360582236692966474, 360582237012071037]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594055597714280, 360594116283414758⟩, ⟨(-1142451174115777022), (-1138523441462480372)⟩, true⟩

def words04 : List Nat := [360582237262198824, 360582237425235296, 360582237604473230, 360582237784135320, 360582237915965093, 360582238010888836, 360582238042080696, 360582238073423321, 360582238102974561, 360582238228501795]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk958A

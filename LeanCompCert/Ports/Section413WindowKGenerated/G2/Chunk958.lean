import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk958

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

def state06 : KState := ⟨⟨360590239128854403, 360590299827649447⟩, ⟨(-776650094168474473), (-772721106334007135)⟩, true⟩

def words05 : List Nat := [360582238350837907, 360582238473419479, 360582238534670593, 360582238579235045, 360582238580400459, 360582238573767879, 360582238667442626, 360582238807150043, 360582238892491261, 360582238978019942]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607305108029367, 360607365819941671⟩, ⟨(-2412676365210802634), (-2408746119890431558)⟩, true⟩

def words06 : List Nat := [360582239153274475, 360582239398392644, 360582239679659003, 360582239961185084, 360582240134217115, 360582240198821167, 360582240325951432, 360582240453501323, 360582240689474736, 360582240952986175]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595238269014025, 360595298994185658⟩, ⟨(-1255716871968394796), (-1251785355412353814)⟩, true⟩

def words07 : List Nat := [360582241161475809, 360582241370137351, 360582241687344067, 360582242078548923, 360582242397113943, 360582242715901530, 360582242964526002, 360582243104808893, 360582243242121189, 360582243379878211]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593041791732696, 360593102529993528⟩, ⟨(-1045110181654840400), (-1041177410040630004)⟩, true⟩

def words08 : List Nat := [360582243625987770, 360582243787658141, 360582243889042456, 360582243990575631, 360582244049599337, 360582244192436062, 360582244309445997, 360582244426717521, 360582244489028632, 360582244603701795]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597580182566336, 360597640933965513⟩, ⟨(-1480353391309744633), (-1476419359794717747)⟩, true⟩

def words09 : List Nat := [360582244826862322, 360582245050427108, 360582245229176792, 360582245299724390, 360582245301018648, 360582245278356312, 360582245267949977, 360582245365625467, 360582245527287473, 360582245689288245]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk958

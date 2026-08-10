import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk958A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk958B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk958A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk958B

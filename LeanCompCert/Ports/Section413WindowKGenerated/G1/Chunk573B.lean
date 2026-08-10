import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk573A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk573B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk573A

def state06 : KState := ⟨⟨362485169787369236, 362485217856140275⟩, ⟨(-15522375664875205), (-13659833243952489)⟩, true⟩

def words05 : List Nat := [371284980747247989, 371284980448723691, 371284980149406085, 371284980128584964, 371284980008931754, 371284979981681541, 371284979953800855, 371284979928403019, 371284979711576372, 371284979718150283]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478744298906106, 362478792384890770⟩, ⟨353115507670957385, 354979037555995567⟩, true⟩

def words06 : List Nat := [371284979947038915, 371284979948978934, 371284979942442025, 371284979935057283, 371284979926983039, 371284979866853410, 371284979742553677, 371284979833923653, 371284979920582774, 371284979922585663]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499141782089770, 362499189885571605⟩, ⟨(-817157793537069001), (-815293259752412795)⟩, true⟩

def words07 : List Nat := [371284979969512387, 371284980125305897, 371284980584140338, 371284980638533017, 371284980640051932, 371284980615506192, 371284980844249634, 371284980968365479, 371284981217330162, 371284981467109878]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495917210019754, 362495965330954621⟩, ⟨(-632153393643812019), (-630287858313010689)⟩, true⟩

def words08 : List Nat := [371284981720809343, 371284981722754141, 371284981952847907, 371284982221565544, 371284982528205203, 371284982584032138, 371284982585490333, 371284982553538304, 371284982790703472, 371284982984274602]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486406767780541, 362486454906192539⟩, ⟨(-86267613912650013), (-84401075481263427)⟩, true⟩

def words09 : List Nat := [371284983400757702, 371284983818043272, 371284984171018527, 371284984172954566, 371284984123962711, 371284984129195350, 371284984437276680, 371284984474878895, 371284984501947110, 371284984529796984]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk573B

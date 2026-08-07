import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk573

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482978546012264, 362483026510226743⟩, ⟨110358716187204163, 112215264365137235⟩, true⟩

def state01 : KState := ⟨⟨362482693478924757, 362482741460371915⟩, ⟨126754015142784955, 128611550843390595⟩, true⟩

def words00 : List Nat := [371284985129612466, 371284985150009359, 371284985171686219, 371284985194034253, 371284985292632532, 371284985294762200, 371284985377849718, 371284985515839932, 371284985596393708, 371284985598407920]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501056965800941, 362501104964734002⟩, ⟨(-925734176231154114), (-923875638326118992)⟩, true⟩

def words01 : List Nat := [371284985784209037, 371284986010210379, 371284986470554773, 371284986525621634, 371284986533646752, 371284986542294839, 371284986751576039, 371284986821726285, 371284987104235292, 371284987387609980]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475296308268924, 362475344324691354⟩, ⟨550891045895071506, 552750586377987370⟩, true⟩

def words02 : List Nat := [371284987619064939, 371284987620998379, 371284987446545652, 371284987353539699, 371284987259598232, 371284987257872950, 371284986849943730, 371284986426602358, 371284986002464520, 371284985883846735]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362458512489553023, 362458560523336576⟩, ⟨1513298738530439122, 1515159274417528680⟩, true⟩

def words03 : List Nat := [371284985853347977, 371284985991800671, 371284986113524030, 371284986115457983, 371284985871094516, 371284985719458453, 371284985566832133, 371284985539479371, 371284985106096379, 371284984647410827]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470925632672530, 362470973683778663⟩, ⟨801457483394481735, 803319012644124131⟩, true⟩

def words04 : List Nat := [371284984187902208, 371284983919261426, 371284983533727321, 371284983234604426, 371284982934825653, 371284982589089695, 371284981884501420, 371284981485311015, 371284981085129677, 371284980990014830]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk573

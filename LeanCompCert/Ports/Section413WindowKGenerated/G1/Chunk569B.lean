import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk569A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk569B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk569A

def state06 : KState := ⟨⟨362499783129955806, 362499830504097446⟩, ⟨(-849921598076255366), (-848098760929951982)⟩, true⟩

def words05 : List Nat := [371284939854703246, 371284940083582925, 371284940502881183, 371284940511839862, 371284940513325429, 371284940475129940, 371284940704408029, 371284940864868230, 371284941127598802, 371284941391179310]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497165533368838, 362497212924838223⟩, ⟨(-700830437740785794), (-699006613516771502)⟩, true⟩

def words06 : List Nat := [371284941655472522, 371284941657396586, 371284941855613500, 371284942110566850, 371284942457449449, 371284942625920630, 371284942761562026, 371284942897859618, 371284943190950891, 371284943408531387]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484451303425539, 362484498712194644⟩, ⟨23614068177043098, 25438878054116532⟩, true⟩

def words07 : List Nat := [371284943845893692, 371284944284002192, 371284944663239803, 371284944678161068, 371284944753718248, 371284944830245082, 371284945172506047, 371284945174428045, 371284945170594531, 371284945164950947]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494587658411583, 362494635084338749⟩, ⟨(-553960117711998591), (-552134330078827807)⟩, true⟩

def words08 : List Nat := [371284945376868760, 371284945444164651, 371284945818871258, 371284946194368539, 371284946508600226, 371284946510521190, 371284946443968334, 371284946476132628, 371284946815459150, 371284946987444875]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502297943923164, 362502345387375834⟩, ⟨(-993394392118727826), (-991567605622609088)⟩, true⟩

def words09 : List Nat := [371284947090871773, 371284947194970530, 371284947606367953, 371284947925132463, 371284948336003880, 371284948747579029, 371284949156501264, 371284949158422739, 371284949462065502, 371284949769656450]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk569B

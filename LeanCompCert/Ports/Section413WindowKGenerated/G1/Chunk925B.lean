import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk925A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk925B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk925A

def state06 : KState := ⟨⟨362479647589517052, 362479777510493996⟩, ⟨485832723039907756, 493952005726891366⟩, true⟩

def words05 : List Nat := [371285114108774127, 371285114130497825, 371285114150838231, 371285114154153783, 371285114109225188, 371285114094548035, 371285114176334418, 371285114179571160, 371285114124582346, 371285114070625013]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486452168766760, 362486582118740199⟩, ⟨(-144032861638859996), (-135910894892497998)⟩, true⟩

def words06 : List Nat := [371285114015204323, 371285114009432162, 371285113980924206, 371285114021245988, 371285114023798529, 371285114016210212, 371285113875452387, 371285113853162009, 371285113919484289, 371285113938695774]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483563534304812, 362483693513721405⟩, ⟨123387745988801617, 131512438438413671⟩, true⟩

def words07 : List Nat := [371285113948212522, 371285113958793035, 371285114045598158, 371285114080217100, 371285114106194707, 371285114133436473, 371285114159254126, 371285114162492762, 371285114052617384, 371285114041248284]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482542639955561, 362482672648232280⟩, ⟨217959310370460971, 226086674841336155⟩, true⟩

def words08 : List Nat := [371285114129400263, 371285114159148528, 371285114185272451, 371285114212493768, 371285114274186978, 371285114293250413, 371285114352298558, 371285114412615188, 371285114449337792, 371285114452691092]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362495444554484781, 362495574592083253⟩, ⟨(-976670495121208065), (-968540415604000353)⟩, true⟩

def words09 : List Nat := [371285114502890729, 371285114581220882, 371285114774400112, 371285114829778899, 371285114865905193, 371285114903070930, 371285115003282987, 371285115073507719, 371285115188673962, 371285115305297970]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk925B

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk925

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477092930347538, 362477222676415436⟩, ⟨721648869221810457, 729751967558040473⟩, true⟩

def state01 : KState := ⟨⟨362495364349977707, 362495494124979917⟩, ⟨(-968540746965675338), (-960434972057745256)⟩, true⟩

def words00 : List Nat := [371285111823738761, 371285111827340898, 371285111869716813, 371285111951775137, 371285112003719289, 371285112006958798, 371285111972085025, 371285112015828966, 371285112163199860, 371285112278798839]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494393066790937, 362494522871343355⟩, ⟨(-878651518133447679), (-870543009391074945)⟩, true⟩

def words01 : List Nat := [371285112387331844, 371285112497036918, 371285112707310515, 371285112870748454, 371285113068686217, 371285113267830470, 371285113465636538, 371285113521987547, 371285113625920368, 371285113731695156]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485283766225884, 362485413599587670⟩, ⟨(-35829793563867505), (-27718619225820423)⟩, true⟩

def words02 : List Nat := [371285113870878190, 371285113874113585, 371285113857817548, 371285113842323344, 371285113842007658, 371285113845635751, 371285113894271801, 371285113970380188, 371285114032637913, 371285114039232483]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493961133346557, 362494090995966898⟩, ⟨(-838794786935739400), (-830680905156048738)⟩, true⟩

def words03 : List Nat := [371285114118275216, 371285114198979938, 371285114326656413, 371285114343413384, 371285114352480210, 371285114362583134, 371285114426829122, 371285114440699787, 371285114539897901, 371285114640565984]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475864330640646, 362475994222442275⟩, ⟨835936132064164963, 844052714428449241⟩, true⟩

def words04 : List Nat := [371285114741893622, 371285114745129909, 371285114690644944, 371285114683647764, 371285114690012955, 371285114693249365, 371285114555166196, 371285114404368426, 371285114252280754, 371285114186941773]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk925

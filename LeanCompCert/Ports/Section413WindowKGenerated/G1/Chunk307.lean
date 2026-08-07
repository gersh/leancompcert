import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk307

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362449307767159966, 362449320852017615⟩, ⟨1111433544979070160, 1111705071200857360⟩, true⟩

def state01 : KState := ⟨⟨362471819070381010, 362471832164082915⟩, ⟨420351302763674197, 420623100548573581⟩, true⟩

def words00 : List Nat := [371285531564759589, 371285530938582948, 371285530102913888, 371285530214761152, 371285530215525775, 371285530060192419, 371285528894879022, 371285528787762882, 371285528779816569, 371285528780837998]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362464064740899882, 362464077843598630⟩, ⟨658641625698391342, 658913699821723618⟩, true⟩

def words01 : List Nat := [371285528335592624, 371285527793802798, 371285527766166419, 371285527767253068, 371285528058763549, 371285528367157898, 371285528665387967, 371285528666374694, 371285527554261901, 371285526857264702]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362449074264125248, 362449087375621423⟩, ⟨1119198954937358192, 1119471299363533850⟩, true⟩

def words02 : List Nat := [371285526336104849, 371285526337091678, 371285525104313018, 371285523519107221, 371285521933637472, 371285520664401753, 371285518865106418, 371285518122661934, 371285517379923472, 371285516640163029]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501821230666713, 362501834351070974⟩, ⟨(-501927963603508024), (-501655345387008114)⟩, true⟩

def words03 : List Nat := [371285515455409432, 371285515209337279, 371285515645893881, 371285515646887747, 371285515442156554, 371285515093862801, 371285514836899285, 371285514837987058, 371285515047908599, 371285515579873323]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468359748857594, 362468372878171937⟩, ⟨526780381883674173, 527053274040464179⟩, true⟩

def words04 : List Nat := [371285516114760346, 371285516115749970, 371285515908564400, 371285516261624726, 371285516586640759, 371285516587628444, 371285515505253992, 371285514318998217, 371285513132427932, 371285512822043172]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362449827959264926, 362449841097495166⟩, ⟨1096694071644150785, 1096967238010586437⟩, true⟩

def words05 : List Nat := [371285512265348141, 371285511969137830, 371285511672609486, 371285511168605027, 371285509257639086, 371285507671255905, 371285506084468620, 371285505551841644, 371285504389657583, 371285503231370673]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466094819571688, 362466107966639833⟩, ⟨596345281888742455, 596618720155213027⟩, true⟩

def words06 : List Nat := [371285502072713536, 371285501699442374, 371285500961716538, 371285501120229488, 371285501121007590, 371285501050885087, 371285499574900283, 371285498651433300, 371285497727503550, 371285497590304286]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478967681775681, 362478980837857856⟩, ⟨200265486010899348, 200539201684003544⟩, true⟩

def words07 : List Nat := [371285496960927503, 371285496319444786, 371285496087507372, 371285496088597601, 371285496355655797, 371285496647231328, 371285496942721160, 371285496943716368, 371285496292028565, 371285496081577285]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362457233153426388, 362457246318316749⟩, ⟨869459730841798473, 869733717676360973⟩, true⟩

def words08 : List Nat := [371285496710748086, 371285496711736765, 371285496148561626, 371285495582102080, 371285495015282503, 371285494668801507, 371285493946338777, 371285493893907843, 371285493841167880, 371285493597227966]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472302230384773, 362472315404242956⟩, ⟨405405070318370237, 405679333315727875⟩, true⟩

def words09 : List Nat := [371285492680512403, 371285492560902924, 371285492661546105, 371285492662535362, 371285491643725593, 371285490446721465, 371285489249407033, 371285488448987840, 371285487237673925, 371285486811168792]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk307

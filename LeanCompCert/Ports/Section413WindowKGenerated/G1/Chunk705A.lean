import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk705A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476928568954569, 362477002372397883⟩, ⟨582087048344775222, 585601035301525218⟩, true⟩

def state01 : KState := ⟨⟨362474960904380346, 362475034729315425⟩, ⟨720822033281436568, 724337535521874076⟩, true⟩

def words00 : List Nat := [371285308736907263, 371285308739322093, 371285308556211764, 371285308364508099, 371285308171817688, 371285308011699653, 371285307750188845, 371285307690466294, 371285307629955856, 371285307563459829]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493141719113432, 362493215565926877⟩, ⟨(-561231055752392613), (-557714010762192933)⟩, true⟩

def words01 : List Nat := [371285307419435982, 371285307356790925, 371285307411302313, 371285307413717510, 371285307266195821, 371285307087374179, 371285306908983659, 371285306911695950, 371285306969729493, 371285307084612628]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480865184791520, 362480939053390937⟩, ⟨304514557784986635, 308033139232296355⟩, true⟩

def words02 : List Nat := [371285307158791744, 371285307161208658, 371285307028692763, 371285307057743615, 371285307094031867, 371285307096447676, 371285306886319743, 371285306677392782, 371285306467445940, 371285306459306609]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475434605952299, 362475508496303386⟩, ⟨687613006126977993, 691133121833706257⟩, true⟩

def words03 : List Nat := [371285306522034960, 371285306647706044, 371285306749895691, 371285306752311754, 371285306586672275, 371285306483450594, 371285306473457756, 371285306475885431, 371285306380197002, 371285306243990283]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486517162210634, 362486591074183159⟩, ⟨(-94204707956573117), (-90683066960952379)⟩, true⟩

def words04 : List Nat := [371285306111881722, 371285306114569280, 371285306021162961, 371285306017624328, 371285306013301736, 371285305977395219, 371285305773375363, 371285305682967007, 371285305698646069, 371285305719376552]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk705A

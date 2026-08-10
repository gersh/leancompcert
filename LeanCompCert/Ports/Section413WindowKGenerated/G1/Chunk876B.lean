import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk876A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk876B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk876A

def state06 : KState := ⟨⟨362479261606881452, 362479377648064965⟩, ⟨501459781660921506, 508328021575403690⟩, true⟩

def words05 : List Nat := [371285176389135087, 371285176402776880, 371285176476390880, 371285176503759007, 371285176560103729, 371285176617643240, 371285176668081435, 371285176671134675, 371285176569910278, 371285176507539930]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471928211465409, 362472044279865486⟩, ⟨1144331630278667407, 1151202256138728729⟩, true⟩

def words06 : List Nat := [371285176443495336, 371285176434711060, 371285176270347416, 371285176107118407, 371285175942683768, 371285175811534119, 371285175629425419, 371285175546166743, 371285175461876454, 371285175365255457]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491917524916530, 362492033620916653⟩, ⟨(-608228686338843495), (-601355640645458545)⟩, true⟩

def words07 : List Nat := [371285175217548496, 371285175201456252, 371285175281254022, 371285175284307260, 371285175227957600, 371285175137177542, 371285175058565067, 371285175061960961, 371285175090517816, 371285175172214592]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483512676561881, 362483628800112564⟩, ⟨128739289868841059, 135614751338141739⟩, true⟩

def words08 : List Nat := [371285175226587321, 371285175229693386, 371285175249809643, 371285175327428856, 371285175421251850, 371285175424313230, 371285175385168145, 371285175347442043, 371285175321331460, 371285175324817071]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483659532267909, 362483775683313085⟩, ⟨115905058712661472, 122782931306638212⟩, true⟩

def words09 : List Nat := [371285175421546501, 371285175537147372, 371285175651774743, 371285175654828333, 371285175610247835, 371285175607178064, 371285175725417628, 371285175728485884, 371285175729295164, 371285175716737335]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk876B

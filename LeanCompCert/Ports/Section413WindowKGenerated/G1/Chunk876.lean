import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk876

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485028838619214, 362485144714943341⟩, ⟨(-3914607438370772), 2939185821344150⟩, true⟩

def state01 : KState := ⟨⟨362469585032133473, 362469700935602509⟩, ⟨1349055603765390140, 1355911775059541686⟩, true⟩

def words00 : List Nat := [371285178351199674, 371285178354249338, 371285178265124970, 371285178177122509, 371285178087996007, 371285178006056930, 371285177867131227, 371285177786135357, 371285177704090355, 371285177613779196]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482101646104634, 362482217577158459⟩, ⟨252438642136476086, 259297230271245504⟩, true⟩

def words01 : List Nat := [371285177439195380, 371285177385461671, 371285177402821690, 371285177405872144, 371285177324052411, 371285177193906077, 371285177062476183, 371285177031636367, 371285176945914964, 371285176915554616]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485494498266696, 362485610456825903⟩, ⟨(-44909338833773728), (-38048340536483374)⟩, true⟩

def words02 : List Nat := [371285176884060219, 371285176853447785, 371285176660552001, 371285176599390956, 371285176536662930, 371285176514681378, 371285176418835814, 371285176324119580, 371285176260249459, 371285176268690010]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474164168970490, 362474280155058538⟩, ⟨948081916588727552, 954945327378333680⟩, true⟩

def words03 : List Nat := [371285176405779156, 371285176544147555, 371285176661967051, 371285176665019253, 371285176630888973, 371285176609298218, 371285176612569116, 371285176615623123, 371285176502794034, 371285176381979788]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485936345464511, 362486052358864301⟩, ⟨(-83646536159448826), (-76780731631074134)⟩, true⟩

def words04 : List Nat := [371285176265445718, 371285176268843622, 371285176283305206, 371285176357807904, 371285176410393120, 371285176413459246, 371285176341114774, 371285176306963676, 371285176363326817, 371285176376483826]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk876

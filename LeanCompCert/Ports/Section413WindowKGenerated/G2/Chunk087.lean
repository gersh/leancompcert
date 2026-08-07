import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk087

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554370973278428, 360554371379236849⟩, ⟨181906315620177825, 181908710162132465⟩, true⟩

def state01 : KState := ⟨⟨360548932807542058, 360548933214478331⟩, ⟨228341282478528045, 228343685532796557⟩, true⟩

def words00 : List Nat := [360575278023405401, 360575268378405492, 360575254099861284, 360575232994117504, 360575211893205826, 360575187451467099, 360575169793091893, 360575165206329917, 360575160620608271, 360575149481474060]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360729045199069971, 360729045606985886⟩, ⟨(-1341695535478551262), (-1341693123886640348)⟩, true⟩

def words01 : List Nat := [360575150826048405, 360575155179213737, 360575172578732912, 360575176927391444, 360575176927488712, 360575169252222379, 360575161578697516, 360575164069474834, 360575181716524428, 360575199359550198]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360454273056387471, 360454273465295914⟩, ⟨1055204081731749391, 1055206501983302279⟩, true⟩

def words02 : List Nat := [360575206979797931, 360575216446841363, 360575220110784515, 360575223773916837, 360575223774004139, 360575223520763228, 360575210255028794, 360575190478341386, 360575170706167114, 360575144771365021]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360471323193704988, 360471323603594674⟩, ⟨906655454427767594, 906657883250530096⟩, true⟩

def words03 : List Nat := [360575130927524803, 360575130084785190, 360575129242227259, 360575119348595781, 360575108050840515, 360575093437800984, 360575078828074180, 360575077204444010, 360575072073935219, 360575060203508923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360649089753641834, 360649090164517181⟩, ⟨(-647891966735560446), (-647889529293245068)⟩, true⟩

def words04 : List Nat := [360575049444520869, 360575058437197335, 360575066971371373, 360575075503611954, 360575075503708664, 360575071382431869, 360575054309836590, 360575050195928571, 360575046082930231, 360575054108147253]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598463318243186, 360598463730111996⟩, ⟨(-204463810901733878), (-204461364761570118)⟩, true⟩

def words05 : List Nat := [360575056084649834, 360575058060712179, 360575072971284426, 360575094560767958, 360575107513245525, 360575120462782235, 360575123380834450, 360575123380939005, 360575123391550177, 360575126055786969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604940641169030, 360604941054022285⟩, ⟨(-260947066633777286), (-260944611864817122)⟩, true⟩

def words06 : List Nat := [360575141633227906, 360575154193677946, 360575158020155918, 360575161845773773, 360575162380777715, 360575169453768362, 360575178203458323, 360575186951171928, 360575186951265247, 360575190214680726]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360796189268982766, 360796189682826185⟩, ⟨(-1940026751972107716), (-1940024288514663206)⟩, true⟩

def words07 : List Nat := [360575192464020360, 360575194712876240, 360575204301421501, 360575207800561433, 360575207800659368, 360575200189698657, 360575192712590073, 360575205027374415, 360575230196554487, 360575255360025290]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583555122071828, 360583555536912940⟩, ⟨(-72454487789475232), (-72452015567259678)⟩, true⟩

def words08 : List Nat := [360575274078632864, 360575279970401900, 360575298707074974, 360575317439513695, 360575326862216296, 360575331380327768, 360575331380421300, 360575327134023916, 360575322888573348, 360575313924403868]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360342366809818335, 360342367225649189⟩, ⟨2049268921078103008, 2049271402005211754⟩, true⟩

def words09 : List Nat := [360575322023340993, 360575330120457597, 360575331561314164, 360575331561419163, 360575320210383075, 360575305597256199, 360575290987421564, 360575281707816758, 360575265441473962, 360575238975877054]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk087

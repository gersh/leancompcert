import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk863A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk863B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk863A

def state06 : KState := ⟨⟨362490063066617163, 362490175561786371⟩, ⟨(-435285335593035800), (-428725640955755204)⟩, true⟩

def words05 : List Nat := [371285210893538629, 371285210918397566, 371285211075571189, 371285211078574321, 371285211057341274, 371285211017373821, 371285211066979967, 371285211098147492, 371285211157715539, 371285211218611145]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487059563627753, 362487172085875959⟩, ⟨(-175940994772096045), (-169378961450460309)⟩, true⟩

def words06 : List Nat := [371285211251878178, 371285211254884263, 371285211142049846, 371285211144499136, 371285211160463542, 371285211163521966, 371285211088644541, 371285211014930755, 371285210996870280, 371285211023002420]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480098098856007, 362480210648161883⟩, ⟨425414864557022806, 431979234987313624⟩, true⟩

def words07 : List Nat := [371285211181669188, 371285211341565813, 371285211476292691, 371285211479303174, 371285211510736287, 371285211550045145, 371285211672699442, 371285211675703477, 371285211619935626, 371285211565445830]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484535425784812, 362484648001953032⟩, ⟨42130018134925473, 48696709073119801⟩, true⟩

def words08 : List Nat := [371285211585588507, 371285211597918400, 371285211677831668, 371285211758992067, 371285211828926248, 371285211831931549, 371285211747582303, 371285211683264202, 371285211683400942, 371285211686512277]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492043473258648, 362492156076886866⟩, ⟨(-606532781576240869), (-599963718243466157)⟩, true⟩

def words09 : List Nat := [371285211682256156, 371285211667483377, 371285211732113318, 371285211784842371, 371285211861732031, 371285211939743158, 371285212016600602, 371285212019619804, 371285212048557563, 371285212132739884]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk863B

import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk584A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk584B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk584A

def state06 : KState := ⟨⟨362506408745769853, 362506458751188159⟩, ⟨(-1256061403978756453), (-1254086706468265047)⟩, true⟩

def words05 : List Nat := [371285004882850767, 371285005038615769, 371285005486396504, 371285005673510893, 371285005813793372, 371285005954687097, 371285006216260418, 371285006333024951, 371285006701323540, 371285007070469933]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486786136385801, 362486836159634758⟩, ⟨(-108900238401243731), (-106924498423825969)⟩, true⟩

def words06 : List Nat := [371285007436616893, 371285007438591397, 371285007511572086, 371285007611184245, 371285007724292436, 371285007726272337, 371285007599394207, 371285007472007127, 371285007450380241, 371285007483907923]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485681064577066, 362485731105647814⟩, ⟨(-44259478231164873), (-42282696123690495)⟩, true⟩

def words07 : List Nat := [371285007636416149, 371285007789716258, 371285007939533420, 371285007941517911, 371285007825988710, 371285007799866447, 371285008037023815, 371285008061236105, 371285008075076645, 371285008089691800]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490023612685732, 362490073671418883⟩, ⟨(-298136588815501835), (-296158773718888775)⟩, true⟩

def words08 : List Nat := [371285008396151342, 371285008590350874, 371285009044669444, 371285009499757782, 371285009872322518, 371285009874297899, 371285009920855521, 371285009987295778, 371285010260693699, 371285010349305757]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483549194879568, 362483599271641269⟩, ⟨80620121068827663, 82598990743412989⟩, true⟩

def words09 : List Nat := [371285010390534400, 371285010432433196, 371285010690159647, 371285010803248039, 371285011003232215, 371285011203994051, 371285011352404010, 371285011354393165, 371285011241875870, 371285011220200986]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk584B

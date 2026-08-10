import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk812A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk812B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk812A

def state06 : KState := ⟨⟨362501410292231253, 362501509426653872⟩, ⟨(-1331813439567396467), (-1326373883013575315)⟩, true⟩

def words05 : List Nat := [371285185569092680, 371285185749804334, 371285186069963454, 371285186189189232, 371285186282851974, 371285186377467132, 371285186531803731, 371285186628028240, 371285186830809467, 371285187034817523]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485735929751517, 362485835089613658⟩, ⟨(-58095548584481616), (-52653924688352590)⟩, true⟩

def words06 : List Nat := [371285187237465233, 371285187265579685, 371285187310742724, 371285187357354135, 371285187449100730, 371285187451913451, 371285187357614596, 371285187258290732, 371285187197490549, 371285187208762083]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466853128314201, 362466952313504878⟩, ⟨1476681884339148099, 1482125566815880183⟩, true⟩

def words07 : List Nat := [371285187347014993, 371285187486434512, 371285187624964592, 371285187627777428, 371285187564455183, 371285187546818428, 371285187535883808, 371285187538696815, 371285187347234668, 371285187126088735]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481398393487962, 362481497603863517⟩, ⟨294426395570304969, 299872125202672163⟩, true⟩

def words08 : List Nat := [371285186903653511, 371285186833734648, 371285186750734260, 371285186787012587, 371285186797534269, 371285186800347933, 371285186625527045, 371285186566781075, 371285186518697147, 371285186521629573]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491279681283571, 362491378917266518⟩, ⟨(-508882104134716793), (-503434292745056821)⟩, true⟩

def words09 : List Nat := [371285186478391041, 371285186411162155, 371285186423829833, 371285186445998650, 371285186498264556, 371285186551644219, 371285186604233980, 371285186607096959, 371285186610084213, 371285186689707878]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk812B

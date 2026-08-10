import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk815A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk815B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk815A

def state06 : KState := ⟨⟨360608430207958868, 360608473600578418⟩, ⟨(-2141356031248618863), (-2138965857036175667)⟩, true⟩

def words05 : List Nat := [360582246521766050, 360582246627680378, 360582246883455803, 360582247125738604, 360582247239562298, 360582247353474013, 360582247431606481, 360582247604272891, 360582247926771861, 360582248249527841]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360612824201694343, 360612867605438952⟩, ⟨(-2499847530666200366), (-2497456449039083428)⟩, true⟩

def words06 : List Nat := [360582248488152686, 360582248683268621, 360582249028335711, 360582249373759715, 360582249620430409, 360582249816332078, 360582249915431426, 360582250014642408, 360582250263796846, 360582250640475435]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581419293535726, 360581462708296423⟩, ⟨61988691437943842, 64380671702904300⟩, true⟩

def words07 : List Nat := [360582250975951852, 360582251311627055, 360582251571926679, 360582251682451068, 360582251706697153, 360582251731267470, 360582251807652509, 360582251887963897, 360582251889005033, 360582251880540882]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360597994743804775, 360598038169593316⟩, ⟨(-1290336594103687824), (-1287943714134132928)⟩, true⟩

def words08 : List Nat := [360582251932474123, 360582252069711302, 360582252257400295, 360582252445306004, 360582252482023936, 360582252483195004, 360582252476601189, 360582252485511305, 360582252609930687, 360582252804612692]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595203660006919, 360595247096936844⟩, ⟨(-1062576217818008785), (-1060182428767706043)⟩, true⟩

def words09 : List Nat := [360582252923924787, 360582253043383094, 360582253282127718, 360582253597403930, 360582253874764773, 360582254152309447, 360582254339357466, 360582254503689230, 360582254663873455, 360582254824430776]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk815B

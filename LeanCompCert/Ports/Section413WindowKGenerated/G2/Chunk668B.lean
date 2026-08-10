import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk668A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk668B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk668A

def state06 : KState := ⟨⟨360589878252386138, 360589906958741313⟩, ⟨(-468295877903841871), (-466999397610389937)⟩, true⟩

def words05 : List Nat := [360582921436709003, 360582921588199811, 360582921962645392, 360582922113953349, 360582922114823275, 360582922075270773, 360582922035551956, 360582922117296393, 360582922222532829, 360582922327975839]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571240021660937, 360571268737006335⟩, ⟨777851164385361473, 779148245808773099⟩, true⟩

def words06 : List Nat := [360582922328829546, 360582922244332265, 360582922003436697, 360582921986034103, 360582921968364331, 360582921851862175, 360582921580454980, 360582921183159722, 360582920785700722, 360582920423051031]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360559946958059447, 360559975682305652⟩, ⟨1533011482712365784, 1534309159377465346⟩, true⟩

def words07 : List Nat := [360582920249586336, 360582919999750763, 360582919749815342, 360582919388419946, 360582918908024373, 360582918358033946, 360582917807783158, 360582917480857518, 360582917249815231, 360582916907774813]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601379337315047, 360601408070458850⟩, ⟨(-1238189466909741111), (-1236891195129070837)⟩, true⟩

def words08 : List Nat := [360582916565522435, 360582916372326774, 360582916485493926, 360582916654171408, 360582916655061291, 360582916619338925, 360582916432970007, 360582916430688137, 360582916647817627, 360582916925235591]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589112490076125, 360589141232220190⟩, ⟨(-417582039465352565), (-416283165612820143)⟩, true⟩

def words09 : List Nat := [360582917031826886, 360582917138528738, 360582917423651448, 360582917821066259, 360582918084615202, 360582918348308656, 360582918498916188, 360582918668508141, 360582918762299156, 360582918856387052]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk668B

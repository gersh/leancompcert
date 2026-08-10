import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk710A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk710B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk710A

def state06 : KState := ⟨⟨360595728747902926, 360595761331468321⟩, ⟨(-952465924491892845), (-950901982862724681)⟩, true⟩

def words05 : List Nat := [360582379474787206, 360582379592510382, 360582379828690099, 360582379867297675, 360582379868235549, 360582379738048527, 360582379607686623, 360582379473367952, 360582379653198969, 360582379842566354]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586722458045085, 360586755051193521⟩, ⟨(-312577113182363342), (-311012490535501760)⟩, true⟩

def words06 : List Nat := [360582379932901426, 360582379933908832, 360582379879378458, 360582379933470820, 360582379934314275, 360582379907057312, 360582379681970245, 360582379358163572, 360582379034173137, 360582378969661877]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360538305908448520, 360538338511099386⟩, ⟨3128592151068264848, 3130157449100427690⟩, true⟩

def words07 : List Nat := [360582378970500509, 360582378870062301, 360582378769525870, 360582378548374347, 360582378129384586, 360582377660868364, 360582377192072462, 360582376710832336, 360582376234969312, 360582375616460957]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572224812806456, 360572257424967193⟩, ⟨717492207238226446, 719058181279751794⟩, true⟩

def words08 : List Nat := [360582374997741763, 360582374576849247, 360582374309227565, 360582374161272149, 360582374013254180, 360582373681206165, 360582373151358858, 360582372763021767, 360582372374399983, 360582372183460368]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360550985273103178, 360551017894889861⟩, ⟨2227530992097866573, 2229097650494139235⟩, true⟩

def words09 : List Nat := [360582372042088848, 360582371800126030, 360582371557966309, 360582371270215947, 360582371138446328, 360582370917486700, 360582370696427891, 360582370350371270, 360582369919079704, 360582369479284997]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk710B

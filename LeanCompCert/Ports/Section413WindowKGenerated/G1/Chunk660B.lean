import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk660A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk660B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk660A

def state06 : KState := ⟨⟨362476579237318131, 362476643708741430⟩, ⟨583002236222381601, 585878789969522299⟩, true⟩

def words05 : List Nat := [371285512300977610, 371285512354159443, 371285512558089973, 371285512658439596, 371285512767677656, 371285512877787414, 371285512954966109, 371285512957217636, 371285512728946568, 371285512597478480]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483483815950153, 362483548307440539⟩, ⟨126884307366172200, 129762186846840382⟩, true⟩

def words06 : List Nat := [371285512521475814, 371285512523735932, 371285512410233087, 371285512278303993, 371285512145487583, 371285512076200811, 371285512079754995, 371285512197657563, 371285512315808028, 371285512318138993]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486279572938446, 362486344084837147⟩, ⟨(-57801566352484185), (-54922338392056177)⟩, true⟩

def words07 : List Nat := [371285512489134440, 371285512691036434, 371285512987330536, 371285512989582496, 371285512980887400, 371285512935993727, 371285512960322315, 371285512962827051, 371285512933041009, 371285512948226139]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484092518371862, 362484157050552456⟩, ⟨86705684033155687, 89586252328118539⟩, true⟩

def words08 : List Nat := [371285512962434134, 371285512964693033, 371285512857198965, 371285512919766993, 371285513051227759, 371285513053480155, 371285512907794801, 371285512719077908, 371285512567007857, 371285512569576940]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362474321527994407, 362474386080452282⟩, ⟨732581943747208141, 735463852266299403⟩, true⟩

def words09 : List Nat := [371285512648266646, 371285512748371314, 371285512847700423, 371285512849992375, 371285512758771460, 371285512738733084, 371285512899023472, 371285512901276257, 371285512779588552, 371285512613769473]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk660B

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk660

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483001739416482, 362483066089226937⟩, ⟨158725218012671002, 161593741643749154⟩, true⟩

def state01 : KState := ⟨⟨362478465161583445, 362478529531440737⟩, ⟨458144515836270295, 461014362661384973⟩, true⟩

def words00 : List Nat := [371285514558557169, 371285514560806760, 371285514404072249, 371285514206000482, 371285514007092377, 371285513859936021, 371285513625237229, 371285513596910418, 371285513567803954, 371285513539358650]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490626006155595, 362490690396304179⟩, ⟨(-344673014267313998), (-341801827908032746)⟩, true⟩

def words01 : List Nat := [371285513435098568, 371285513382946889, 371285513481890937, 371285513484151461, 371285513418859511, 371285513312637507, 371285513205498588, 371285513194888110, 371285513147086392, 371285513228010636]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483860995574066, 362483925406031196⟩, ⟨101941903720545293, 104814430951311841⟩, true⟩

def words02 : List Nat := [371285513286709583, 371285513288974824, 371285513195165234, 371285513251184620, 371285513356018716, 371285513358268841, 371285513157608813, 371285512956232719, 371285512779366340, 371285512781935351]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475177692338182, 362475242123095584⟩, ⟨675341251182200998, 678215118944044248⟩, true⟩

def words03 : List Nat := [371285512831008763, 371285512905038114, 371285512907455549, 371285512909706233, 371285512629350735, 371285512407795354, 371285512190049774, 371285512192340560, 371285512038597151, 371285511885647735]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490181869463648, 362490246320369886⟩, ⟨(-315565375602065505), (-312690177110805251)⟩, true⟩

def words04 : List Nat := [371285511805292750, 371285511807798549, 371285511937469153, 371285512109105589, 371285512185305073, 371285512187556296, 371285511958080565, 371285511958895441, 371285512174552936, 371285512248560061]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk660

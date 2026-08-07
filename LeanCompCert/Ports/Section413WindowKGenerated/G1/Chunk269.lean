import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk269

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362533019770859209, 362533029705997049⟩, ⟨(-1285836358818895680), (-1285655687502300096)⟩, true⟩

def state01 : KState := ⟨⟨362514818874015310, 362514828816880338⟩, ⟨(-796309316299890123), (-796128437083505149)⟩, true⟩

def words00 : List Nat := [371285239050520683, 371285239051374970, 371285239669535564, 371285240669913289, 371285242082796640, 371285242260653152, 371285242434900588, 371285242609431147, 371285243961299191, 371285245061647032]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362466608929556788, 362466618880113627⟩, ⟨501396332030190743, 501577418273407961⟩, true⟩

def words01 : List Nat := [371285247032108850, 371285249002781585, 371285250970204499, 371285251098890523, 371285251293428199, 371285251488352542, 371285252395258631, 371285252396113625, 371285251719083999, 371285251027894958]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480538235089980, 362480548193316795⟩, ⟨126523597668903616, 126704890425786222⟩, true⟩

def words02 : List Nat := [371285251023412359, 371285251213987569, 371285252045683109, 371285252877651836, 371285253463302583, 371285253464157537, 371285252338714527, 371285252466071763, 371285253164226538, 371285253165111292]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362462397883524987, 362462407849528227⟩, ⟨615261725146331563, 615443227362210613⟩, true⟩

def words03 : List Nat := [371285252991046790, 371285252780417820, 371285253336045801, 371285253475252073, 371285254026503490, 371285254578068736, 371285255034789993, 371285255035645198, 371285253656689618, 371285252809712422]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362456764903363033, 362456774877004178⟩, ⟨767015035453784530, 767196743474112870⟩, true⟩

def words04 : List Nat := [371285252118088065, 371285252118945315, 371285250876821641, 371285249361046295, 371285247845046653, 371285246446925796, 371285244373434817, 371285243677046012, 371285242980432016, 371285242288635871]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362508860367666484, 362508870349034270⟩, ⟨(-637168976855262980), (-636987060561552636)⟩, true⟩

def words05 : List Nat := [371285241553138458, 371285241874331737, 371285243571324075, 371285243572179746, 371285243435386342, 371285243051628098, 371285242852922170, 371285242853864728, 371285243231572626, 371285244108888818]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362496191515236166, 362496201504330491⟩, ⟨(-295648686085478738), (-295466561445432932)⟩, true⟩

def words06 : List Nat := [371285244683184651, 371285244684047131, 371285245119083938, 371285245894253671, 371285247080266231, 371285247081122480, 371285246622175634, 371285246061769059, 371285246124730575, 371285246531899160]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466677501256763, 362466687498071518⟩, ⟨500531221290156215, 500713554189093375⟩, true⟩

def words07 : List Nat := [371285247508816678, 371285248485997231, 371285249337960749, 371285249338817383, 371285248359881194, 371285247624003776, 371285247320789815, 371285247321661887, 371285246878641690, 371285246191703434]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495145630786662, 362495155635263137⟩, ⟨(-267602278699858049), (-267419739047795367)⟩, true⟩

def words08 : List Nat := [371285246189623582, 371285246190576095, 371285246795820075, 371285247401722218, 371285247656906529, 371285247657763648, 371285246289951647, 371285246293063028, 371285247529928234, 371285247897904470]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486525677314296, 362486535689630141⟩, ⟨(-34718227585004993), (-34535476310169989)⟩, true⟩

def words09 : List Nat := [371285248267085963, 371285248636549665, 371285250377534822, 371285251649891430, 371285253332924049, 371285255016153963, 371285256696196876, 371285256697054412, 371285256596834487, 371285256645286963]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk269

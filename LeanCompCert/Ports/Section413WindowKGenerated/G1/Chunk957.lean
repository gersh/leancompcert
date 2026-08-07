import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk957

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488168719802322, 362488307964379251⟩, ⟨(-302667754008930720), (-293670752318926570)⟩, true⟩

def state01 : KState := ⟨⟨362489295646674604, 362489434921115500⟩, ⟨(-410510010188795640), (-401510150361402342)⟩, true⟩

def words00 : List Nat := [371285239480190504, 371285239492424331, 371285239496032576, 371285239500859594, 371285239537118468, 371285239540868755, 371285239640762716, 371285239747828127, 371285239847625388, 371285239894939184]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497783684467937, 362497922989297818⟩, ⟨(-1222965520561454810), (-1213962752050534130)⟩, true⟩

def words01 : List Nat := [371285239953582723, 371285240013959731, 371285240181826849, 371285240205215431, 371285240211197377, 371285240218167671, 371285240333074952, 371285240414941116, 371285240549724947, 371285240686020058]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493814658982636, 362493953994070390⟩, ⟨(-843037461289478822), (-834031796337879576)⟩, true⟩

def words02 : List Nat := [371285240820583902, 371285240881883544, 371285241051333048, 371285241222521533, 371285241394698319, 371285241449786582, 371285241491304988, 371285241533997237, 371285241655588206, 371285241750425825]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484329471191725, 362484468836482510⟩, ⟨65081933703466475, 74090490148481869⟩, true⟩

def words03 : List Nat := [371285241952953796, 371285242156895008, 371285242336647267, 371285242382105631, 371285242445211742, 371285242510007012, 371285242682267052, 371285242710114656, 371285242712667755, 371285242708324462]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362497106783253525, 362497246178608211⟩, ⟨(-1158259700967921346), (-1149248266058438820)⟩, true⟩

def words04 : List Nat := [371285242774707331, 371285242797666654, 371285242910578633, 371285243024938983, 371285243127583720, 371285243141279177, 371285243263042405, 371285243386509419, 371285243582271643, 371285243711103345]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362497040644471692, 362497180070527494⟩, ⟨(-1151936232694399508), (-1142921858009854094)⟩, true⟩

def words05 : List Nat := [371285243839437581, 371285243968910286, 371285244142093623, 371285244262370306, 371285244387180655, 371285244513230951, 371285244628407575, 371285244665074829, 371285244791991352, 371285244920957107]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484948833208317, 362485088289111834⟩, ⟨6034861917982438, 15052094977473516⟩, true⟩

def words06 : List Nat := [371285245099194839, 371285245133088368, 371285245161804060, 371285245191623970, 371285245247966113, 371285245266713836, 371285245329121963, 371285245392886604, 371285245454842171, 371285245458319076]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498276381129584, 362498415867358659⟩, ⟨(-1270405347284732329), (-1261385209792251693)⟩, true⟩

def words07 : List Nat := [371285245513681054, 371285245572383238, 371285245738524989, 371285245815280851, 371285245872721543, 371285245931254175, 371285246043953136, 371285246114211376, 371285246253993201, 371285246395231701]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492458753365531, 362492598269918079⟩, ⟨(-713208361457691880), (-704185319430141098)⟩, true⟩

def words08 : List Nat := [371285246514343109, 371285246517701613, 371285246598476258, 371285246696359460, 371285246825294907, 371285246830095297, 371285246832630691, 371285246827512974, 371285246921272208, 371285247001850827]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481120685507453, 362481260232321277⟩, ⟨372972259140740142, 381998200051189394⟩, true⟩

def words09 : List Nat := [371285247189990853, 371285247379539386, 371285247558476812, 371285247603676716, 371285247625103712, 371285247648145584, 371285247741308168, 371285247744674357, 371285247725250367, 371285247687436634]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk957

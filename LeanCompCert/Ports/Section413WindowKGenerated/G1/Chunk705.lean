import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk705

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476928568954569, 362477002372397883⟩, ⟨582087048344775222, 585601035301525218⟩, true⟩

def state01 : KState := ⟨⟨362474960904380346, 362475034729315425⟩, ⟨720822033281436568, 724337535521874076⟩, true⟩

def words00 : List Nat := [371285308736907263, 371285308739322093, 371285308556211764, 371285308364508099, 371285308171817688, 371285308011699653, 371285307750188845, 371285307690466294, 371285307629955856, 371285307563459829]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493141719113432, 362493215565926877⟩, ⟨(-561231055752392613), (-557714010762192933)⟩, true⟩

def words01 : List Nat := [371285307419435982, 371285307356790925, 371285307411302313, 371285307413717510, 371285307266195821, 371285307087374179, 371285306908983659, 371285306911695950, 371285306969729493, 371285307084612628]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480865184791520, 362480939053390937⟩, ⟨304514557784986635, 308033139232296355⟩, true⟩

def words02 : List Nat := [371285307158791744, 371285307161208658, 371285307028692763, 371285307057743615, 371285307094031867, 371285307096447676, 371285306886319743, 371285306677392782, 371285306467445940, 371285306459306609]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475434605952299, 362475508496303386⟩, ⟨687613006126977993, 691133121833706257⟩, true⟩

def words03 : List Nat := [371285306522034960, 371285306647706044, 371285306749895691, 371285306752311754, 371285306586672275, 371285306483450594, 371285306473457756, 371285306475885431, 371285306380197002, 371285306243990283]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486517162210634, 362486591074183159⟩, ⟨(-94204707956573117), (-90683066960952379)⟩, true⟩

def words04 : List Nat := [371285306111881722, 371285306114569280, 371285306021162961, 371285306017624328, 371285306013301736, 371285305977395219, 371285305773375363, 371285305682967007, 371285305698646069, 371285305719376552]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480280609046537, 362480354543124424⟩, ⟨345831314490519923, 349354515122333157⟩, true⟩

def words05 : List Nat := [371285305724970117, 371285305731373256, 371285305820748268, 371285305840789196, 371285305900073309, 371285305960261457, 371285306002576329, 371285306004993159, 371285305779614497, 371285305712556430]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362459499092634034, 362459573048216487⟩, ⟨1812309241409397077, 1815833959517212795⟩, true⟩

def words06 : List Nat := [371285305727783197, 371285305730200103, 371285305548274017, 371285305355093889, 371285305161010214, 371285304975357793, 371285304711756194, 371285304478223538, 371285304243876754, 371285304009808059]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486935450960183, 362487009428366882⟩, ⟨(-123982468361795513), (-120456210004630227)⟩, true⟩

def words07 : List Nat := [371285303646836785, 371285303485559082, 371285303359375129, 371285303361835079, 371285303245635536, 371285303095375045, 371285302944093697, 371285302891921490, 371285302763588252, 371285302790461432]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476028475098361, 362476102474344429⟩, ⟨645822405485779978, 649350205376570280⟩, true⟩

def words08 : List Nat := [371285302792300267, 371285302777742489, 371285302495053904, 371285302414055220, 371285302331837615, 371285302297230626, 371285302043942534, 371285301753548776, 371285301462155948, 371285301372281482]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471667301981719, 362471741323003353⟩, ⟨953749602286518101, 957278939424892155⟩, true⟩

def words09 : List Nat := [371285301291612968, 371285301342274240, 371285301392359631, 371285301394778574, 371285301214448818, 371285301044382360, 371285300876556701, 371285300878991389, 371285300704096986, 371285300514779910]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk705

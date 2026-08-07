import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk126

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471462593783577, 362471464634278336⟩, ⟨164407559984972575, 164424957756736371⟩, true⟩

def state01 : KState := ⟨⟨362442041016015543, 362442043059854640⟩, ⟨535393950626784259, 535411390554843123⟩, true⟩

def words00 : List Nat := [371284518446872546, 371284518447248088, 371284515320350504, 371284512198403406, 371284509076811491, 371284507842525775, 371284504480194817, 371284503729427636, 371284502978651058, 371284502329525921]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 12600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 12600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362603936920764297, 362603938967996475⟩, ⟨(-1506743207516138086), (-1506725724783802330)⟩, true⟩

def words01 : List Nat := [371284501867137399, 371284504771321643, 371284513944374459, 371284519424939901, 371284523792726631, 371284528159941491, 371284534412929685, 371284537610258700, 371284547071794758, 371284556531994273]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 12610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 12600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362499221122010307, 362499223172642259⟩, ⟨(-185052676144639637), (-185035150489762475)⟩, true⟩

def words02 : List Nat := [371284564639034152, 371284564639410480, 371284568217338470, 371284572038703707, 371284577262463581, 371284577262840075, 371284575301953472, 371284572648486101, 371284572724827096, 371284573885136143]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 12620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 12600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362419836571138990, 362419838625165505⟩, ⟨818240802836102948, 818258371381559756⟩, true⟩

def words03 : List Nat := [371284578966280030, 371284584046774523, 371284589139388065, 371284589139764819, 371284585900478827, 371284582927712658, 371284583226966407, 371284583227343302, 371284579377279657, 371284574255812781]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 12630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 12600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491928663861371, 362491930721266503⟩, ⟨(-93006691346820570), (-92989080078699306)⟩, true⟩

def words04 : List Nat := [371284570257095238, 371284570257517344, 371284573243994648, 371284577264149847, 371284580395389557, 371284580395766551, 371284576260756299, 371284577311736468, 371284579805451614, 371284580386899363]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 12640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 12600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362538790086242744, 362538792147075783⟩, ⟨(-685909791884712804), (-685892137235815108)⟩, true⟩

def words05 : List Nat := [371284580981666670, 371284581576463328, 371284588401977492, 371284592869685443, 371284599214606506, 371284605558680550, 371284611916589921, 371284611916967108, 371284614252677418, 371284618532255800]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 12650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 12600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470008147475189, 362470010211672451⟩, ⟨185219009597820528, 185236706855558698⟩, true⟩

def words06 : List Nat := [371284625989971109, 371284627588135712, 371284627588425864, 371284627501982614, 371284627584683945, 371284627585099418, 371284626763435437, 371284628887929695, 371284630314420740, 371284630314818115]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 12660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 12600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362519560467497681, 362519562535113344⟩, ⟨(-442797883870304151), (-442780143284522145)⟩, true⟩

def words07 : List Nat := [371284634220878084, 371284639280170451, 371284646379109822, 371284646379487642, 371284645195691685, 371284643435872627, 371284642497165934, 371284642497581866, 371284642965026296, 371284645719145793]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 12670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 12600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362448213984786792, 362448216055817221⟩, ⟨461937477147761317, 461955261050024461⟩, true⟩

def words08 : List Nat := [371284648370645010, 371284648371024006, 371284644769042242, 371284644345104744, 371284644331871249, 371284644332249476, 371284636478578569, 371284628636206550, 371284620794910767, 371284619149674591]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 12680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 12600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362429860700255880, 362429862774691819⟩, ⟨695021186866859126, 695039014002592054⟩, true⟩

def words09 : List Nat := [371284616281518187, 371284615152692572, 371284614023920242, 371284612907540761, 371284606293952081, 371284601547466738, 371284598242953867, 371284598243338784, 371284594565277578, 371284590256109346]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 12690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 12600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 12600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk126

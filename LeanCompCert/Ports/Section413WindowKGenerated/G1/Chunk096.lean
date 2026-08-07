import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk096

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362414910837369901, 362414911993071827⟩, ⟨645291257634957790, 645298769690715564⟩, true⟩

def state01 : KState := ⟨⟨362320491343115329, 362320492501309410⟩, ⟨1552339842956808781, 1552347378950462371⟩, true⟩

def words00 : List Nat := [371282127456533361, 371282127456813260, 371282116870577175, 371282103292843231, 371282089717828090, 371282077279125120, 371282059495285583, 371282048719840972, 371282037946543148, 371282027088088855]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362535033209226855, 362535034369956515⟩, ⟨(-510621090448241775), (-510613530074844247)⟩, true⟩

def words01 : List Nat := [371282010281021636, 371281997808738040, 371281985338905424, 371281983684988193, 371281975972672425, 371281966560660025, 371281957150488658, 371281955803846652, 371281956040113611, 371281961557351293]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362464291580635918, 362464292743896073⟩, ⟨170017583272700865, 170025168002513265⟩, true⟩

def words02 : List Nat := [371281967148995778, 371281967149277099, 371281967757704232, 371281973458327177, 371281977852911623, 371281977853192279, 371281967889123074, 371281957839129632, 371281948524259271, 371281948524581693]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362364332364481507, 362364333530277454⟩, ⟨1133723894029132081, 1133731503191486147⟩, true⟩

def words03 : List Nat := [371281955635735281, 371281964578378210, 371281973265446765, 371281973265727541, 371281967615198126, 371281963226396285, 371281961786075908, 371281961786356968, 371281952733527996, 371281940532683210]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362520222095877398, 362520223264190668⟩, ⟨(-369585560348801720), (-369577926906485198)⟩, true⟩

def words04 : List Nat := [371281928334243458, 371281924821640894, 371281917933490513, 371281919865646083, 371281920166333164, 371281920166620566, 371281914683480394, 371281914554152131, 371281925033131878, 371281929001740509]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502114070909259, 362502115241787297⟩, ⟨(-194684202281863560), (-194676544076625970)⟩, true⟩

def words05 : List Nat := [371281932873357008, 371281936744263724, 371281945106088567, 371281948171530263, 371281954437137389, 371281960701557152, 371281965207877480, 371281965208160881, 371281962390082703, 371281964476434164]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362407578790846723, 362407579964232307⟩, ⟨719359593801444633, 719367276242785337⟩, true⟩

def words06 : List Nat := [371281977272698331, 371281977272980176, 371281975815161329, 371281974270162396, 371281974387420734, 371281974387734089, 371281971745928965, 371281972573908683, 371281972574121103, 371281971616377373]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362599432982470593, 362599434158409631⟩, ⟨(-1136956980539342880), (-1136949273393441638)⟩, true⟩

def words07 : List Nat := [371281963997571902, 371281964071139860, 371281970524102836, 371281970524389779, 371281968232406069, 371281964303963906, 371281967119375664, 371281968585688279, 371281980720753422, 371281992853441814]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362533736075745002, 362533737254234285⟩, ⟨(-501180066726149256), (-501172334880857370)⟩, true⟩

def words08 : List Nat := [371282003067263501, 371282003067545994, 371282007509951516, 371282013386745908, 371282020796692482, 371282020796975253, 371282017177759215, 371282013461598151, 371282016682715878, 371282022020008627]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475212761716174, 362475213942748616⟩, ⟨66400224608036256, 66407981109626994⟩, true⟩

def words09 : List Nat := [371282032648120614, 371282043274150144, 371282053696618343, 371282053696901452, 371282052400455638, 371282051681886635, 371282060882722264, 371282060883006635, 371282060831917914, 371282060126368166]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk096

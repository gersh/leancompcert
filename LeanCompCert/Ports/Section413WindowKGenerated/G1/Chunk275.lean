import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk275

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362529450201296027, 362529460603848467⟩, ⟨(-1212830978185311374), (-1212637592582503234)⟩, true⟩

def state01 : KState := ⟨⟨362496318970664696, 362496329381126570⟩, ⟨(-301747794784900064), (-301554191632796560)⟩, true⟩

def words00 : List Nat := [371285367834955858, 371285367835831274, 371285367948657764, 371285368282333752, 371285369014568268, 371285369015446143, 371285368397716524, 371285367745667993, 371285367759186981, 371285368158647097]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362433740967605710, 362433751385951760⟩, ⟨1420184717848682180, 1420378537934815994⟩, true⟩

def words01 : List Nat := [371285368857696482, 371285369557055391, 371285370247449955, 371285370248325906, 371285369180321420, 371285368511627101, 371285367842549236, 371285367726572988, 371285365852702566, 371285363978173229]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362454582527091926, 362454592953281827⟩, ⟨846537984397398945, 846732020386133839⟩, true⟩

def words02 : List Nat := [371285362103382409, 371285360796041723, 371285359031495847, 371285358110347154, 371285357188986144, 371285356033996908, 371285353122201668, 371285351527910830, 371285349933274739, 371285349655802210]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466413140011390, 362466423574199031⟩, ⟨520722322198544589, 520916578404802739⟩, true⟩

def words03 : List Nat := [371285348539311701, 371285347133252522, 371285345726952268, 371285344995435223, 371285343769952988, 371285342943786950, 371285342117375079, 371285341170568426, 371285339168390298, 371285338482637841]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362453467595963270, 362453478037952500⟩, ⟨877372244557860691, 877566715660442103⟩, true⟩

def words04 : List Nat := [371285338425393542, 371285338426270482, 371285337579450171, 371285336731551452, 371285335883376373, 371285335088809946, 371285333637077409, 371285332970631877, 371285332303953761, 371285331639246890]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485310474249465, 362485320924191552⟩, ⟨70100057564009, 264790300255507⟩, true⟩

def words05 : List Nat := [371285330642530133, 371285330802454120, 371285332041152653, 371285332042030837, 371285331874353639, 371285331281807533, 371285330937680737, 371285330938655721, 371285330531318690, 371285330531967324]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468738463723280, 362468748921574089⟩, ⟨456752252222850293, 456947160471526867⟩, true⟩

def words06 : List Nat := [371285330532275243, 371285330531506477, 371285328778333970, 371285328098405504, 371285327418104367, 371285326912999686, 371285325699825762, 371285324479912590, 371285323259722378, 371285322993408385]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362427223126632373, 362427233592390947⟩, ⟨1601745657843860181, 1601940784149701719⟩, true⟩

def words07 : List Nat := [371285322930782265, 371285323469606467, 371285323757078355, 371285323757958511, 371285322699940571, 371285322052598663, 371285321404838346, 371285321137339751, 371285319119666663, 371285317014586368]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362465884164716779, 362465894638332191⟩, ⟨535424912667580440, 535620255704839802⟩, true⟩

def words08 : List Nat := [371285314909261369, 371285314116204663, 371285312667514273, 371285312530994896, 371285312394207033, 371285312040704549, 371285310437487761, 371285309337299511, 371285308236738458, 371285308203236318]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362450000557997768, 362450011039627963⟩, ⟨973858087540968700, 974053651745770206⟩, true⟩

def words09 : List Nat := [371285307500276034, 371285306612662025, 371285305844432680, 371285305845426894, 371285305614515002, 371285305698122552, 371285305780486476, 371285305781365002, 371285304116237469, 371285302838604260]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk275

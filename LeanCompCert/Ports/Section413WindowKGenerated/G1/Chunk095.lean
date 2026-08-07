import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk095

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362619585198794328, 362619586329405478⟩, ⟨(-1309821117798599038), (-1309813845364817400)⟩, true⟩

def state01 : KState := ⟨⟨362513798674211518, 362513799807321897⟩, ⟨(-304763991723887891), (-304756695534867127)⟩, true⟩

def words00 : List Nat := [371281740106399997, 371281740106676771, 371281743284473677, 371281746796381352, 371281753624947454, 371281753625229114, 371281751716866297, 371281749715392879, 371281753887392040, 371281757257060635]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362420557958687536, 362420559094300826⟩, ⟨582951184969311292, 582958504973428182⟩, true⟩

def words01 : List Nat := [371281771680699334, 371281786101420009, 371281798008680202, 371281798008957393, 371281797675887518, 371281797671709633, 371281806510144996, 371281806510422337, 371281800663995283, 371281794231377867]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362500713826977061, 362500714965071837⟩, ⟨(-180007594451916783), (-180000250811115169)⟩, true⟩

def words02 : List Nat := [371281792404780812, 371281792405089308, 371281801263600975, 371281810193784744, 371281817282155132, 371281817282434409, 371281816485664935, 371281818285569302, 371281827215486642, 371281829197491194]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362565406401135673, 362565407541759910⟩, ⟨(-796727371890861274), (-796720004131456794)⟩, true⟩

def words03 : List Nat := [371281830967929664, 371281832738085088, 371281845513610038, 371281854323133333, 371281866436733318, 371281878547902333, 371281887397062507, 371281887397340930, 371281893914149448, 371281902667623923]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494242434491123, 362494243577595902⟩, ⟨(-117528664130370086), (-117521272693746706)⟩, true⟩

def words04 : List Nat := [371281913499703782, 371281914053753764, 371281914523262251, 371281914992767757, 371281916780744669, 371281916781051069, 371281921735649260, 371281929701332014, 371281937684879113, 371281938973607446]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362628073913628975, 362628075059252004⟩, ⟨(-1396017156962910355), (-1396009741464150121)⟩, true⟩

def words05 : List Nat := [371281951234119740, 371281963492211569, 371281983571255576, 371281992820933137, 371282000384736532, 371282007947035911, 371282023410406202, 371282033658865530, 371282048935353370, 371282064208769403]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362555761434897531, 362555762583037041⟩, ⟨(-704416718215600354), (-704409278646371200)⟩, true⟩

def words06 : List Nat := [371282079398353921, 371282085654011133, 371282101118318655, 371282116579532587, 371282135326937495, 371282139532291430, 371282143771652558, 371282148010224626, 371282156597487899, 371282164288329449]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362452069010041879, 362452070160689769⟩, ⟨288799781307916546, 288807244895126866⟩, true⟩

def words07 : List Nat := [371282178502385371, 371282192713581206, 371282206846084170, 371282206846363216, 371282209202734846, 371282211939373184, 371282223319744641, 371282223320023739, 371282220201604551, 371282217054728927]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362437600290276882, 362437601443427675⟩, ⟨427316045433831093, 427323533011699113⟩, true⟩

def words08 : List Nat := [371282213908392126, 371282213294117431, 371282207299503758, 371282204355626181, 371282201412275253, 371282196689505233, 371282177493020194, 371282169176821018, 371282160862215204, 371282160727370501]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362414910837369901, 362414911993071827⟩, ⟨645291257634957790, 645298769690715564⟩, true⟩

def words09 : List Nat := [371282156081632537, 371282150773374838, 371282149106928612, 371282149107240748, 371282150791944248, 371282152520871758, 371282152521084892, 371282152289309869, 371282137617233929, 371282130614914610]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk095

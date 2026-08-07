import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk791

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485603613810982, 362485697354275391⟩, ⟨(-44065962237638211), (-39058921761446727)⟩, true⟩

def state01 : KState := ⟨⟨362471031443934860, 362471125209055919⟩, ⟨1108611965543503929, 1113620956484111681⟩, true⟩

def words00 : List Nat := [371285203570921057, 371285203530652353, 371285203276609224, 371285203183667929, 371285203089345883, 371285203025088272, 371285202775004365, 371285202494641609, 371285202213198811, 371285202076158487]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477463835416378, 362477557625173239⟩, ⟨599762316782472231, 604773256783508615⟩, true⟩

def words01 : List Nat := [371285201900073197, 371285201884767848, 371285201868490467, 371285201852925062, 371285201703757360, 371285201605139992, 371285201538820749, 371285201541573595, 371285201465597251, 371285201372099219]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477229070324655, 362477322884555742⟩, ⟨618331855208174657, 623344731733129861⟩, true⟩

def words02 : List Nat := [371285201277376655, 371285201232381421, 371285201106372802, 371285201063646860, 371285201020098265, 371285200949626108, 371285200665509929, 371285200519247971, 371285200371460035, 371285200361261583]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479858439315116, 362479952278398273⟩, ⟨410275755786353946, 415290598982501206⟩, true⟩

def words03 : List Nat := [371285200263764211, 371285200165290460, 371285200123831557, 371285200133750507, 371285200135713077, 371285200127950099, 371285200119246847, 371285200108879778, 371285199884932015, 371285199821979048]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473470853943602, 362473564717396259⟩, ⟨915852975084437249, 920869747010394679⟩, true⟩

def words04 : List Nat := [371285199811214808, 371285199813995446, 371285199737105660, 371285199639707375, 371285199541238806, 371285199448663934, 371285199275494071, 371285199262875649, 371285199249393805, 371285199205671817]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499089987133197, 362499183875324470⟩, ⟨(-1112019304653583722), (-1107000574542102430)⟩, true⟩

def words05 : List Nat := [371285199072995916, 371285199088774596, 371285199262533827, 371285199271488757, 371285199273623841, 371285199258844857, 371285199330678404, 371285199350931567, 371285199529446935, 371285199709200469]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479064492612711, 362479158405515619⟩, ⟨473246298391648582, 478266984799530530⟩, true⟩

def words06 : List Nat := [371285199887892773, 371285199890626441, 371285199866197776, 371285199879093568, 371285199920862677, 371285199923600454, 371285199793984420, 371285199635364470, 371285199475601358, 371285199418333600]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473863833116918, 362473957770576484⟩, ⟨885047901421495913, 890070532107930045⟩, true⟩

def words07 : List Nat := [371285199388942558, 371285199436941257, 371285199481675751, 371285199484412428, 371285199349042191, 371285199262079236, 371285199173708454, 371285199152399998, 371285199012455151, 371285198873533139]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483493853627373, 362483587815565249⟩, ⟨122555524878899210, 127580093882963644⟩, true⟩

def words08 : List Nat := [371285198750784989, 371285198753828151, 371285198759543572, 371285198817304879, 371285198848102828, 371285198850845357, 371285198757239843, 371285198792407157, 371285198875922028, 371285198878753568]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489538057817936, 362489632044780421⟩, ⟨(-356114849407775378), (-351088298589131218)⟩, true⟩

def words09 : List Nat := [371285198860511263, 371285198809212889, 371285198861768701, 371285198899357271, 371285198969714625, 371285199041106912, 371285199111589893, 371285199114373013, 371285199108227289, 371285199167688098]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk791

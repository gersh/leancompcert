import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk791A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk791B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk791A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk791B

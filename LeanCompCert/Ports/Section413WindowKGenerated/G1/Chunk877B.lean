import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk877A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk877B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk877A

def state06 : KState := ⟨⟨362490563488743928, 362490679804941117⟩, ⟨(-489605622504223038), (-482713261109042914)⟩, true⟩

def words05 : List Nat := [371285178576332560, 371285178720170298, 371285178862937142, 371285178906300141, 371285178988542888, 371285179072263264, 371285179272619129, 371285179357442959, 371285179422465452, 371285179488614856]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495076844561258, 362495193188102852⟩, ⟨(-885701870889248011), (-878807109611192867)⟩, true⟩

def words06 : List Nat := [371285179625875927, 371285179699560693, 371285179837867331, 371285179977378496, 371285180095135612, 371285180105804249, 371285180245155266, 371285180386156706, 371285180571179328, 371285180688420598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490372922985641, 362490489294399789⟩, ⟨(-472811797987467603), (-465914590200798477)⟩, true⟩

def words07 : List Nat := [371285180789220421, 371285180891016719, 371285181045429065, 371285181136265918, 371285181264296143, 371285181393551572, 371285181520199222, 371285181523255788, 371285181537184489, 371285181601502684]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476767246588317, 362476883645181129⟩, ⟨721580824201034391, 728480417876229101⟩, true⟩

def words08 : List Nat := [371285181763026003, 371285181766083039, 371285181754887166, 371285181734222881, 371285181713909073, 371285181717309834, 371285181655989143, 371285181649665623, 371285181642338808, 371285181633766119]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494074586079203, 362494191012317755⟩, ⟨(-797932588645231149), (-791030567811460043)⟩, true⟩

def words09 : List Nat := [371285181541336501, 371285181486952004, 371285181502497593, 371285181505608370, 371285181471773550, 371285181417411197, 371285181433819413, 371285181444387821, 371285181549080082, 371285181655159962]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk877B

import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk733A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk733B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk733A

def state06 : KState := ⟨⟨362471627977251023, 362471708138183916⟩, ⟨993602044166187838, 997573391356471718⟩, true⟩

def words05 : List Nat := [371285306799480550, 371285306957075362, 371285307079312122, 371285307081832150, 371285306956354843, 371285306847765711, 371285306800065877, 371285306802587057, 371285306649307156, 371285306466855624]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486353232379343, 362486433415840976⟩, ⟨(-86686518156683094), (-82713518141587782)⟩, true⟩

def words06 : List Nat := [371285306283430092, 371285306286207219, 371285306287735210, 371285306383146283, 371285306449231736, 371285306451752182, 371285306270134166, 371285306141466403, 371285306065270804, 371285306083268958]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495979966697744, 362496060173092444⟩, ⟨(-793046738734516930), (-789072056003084186)⟩, true⟩

def words07 : List Nat := [371285306086041201, 371285306089661790, 371285306259603473, 371285306364041132, 371285306517652450, 371285306672258984, 371285306827659475, 371285306830186040, 371285306939471860, 371285307089106084]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478850472667302, 362478930701536840⟩, ⟨463971925264988734, 467948257317992736⟩, true⟩

def words08 : List Nat := [371285307256592740, 371285307259114087, 371285307179334902, 371285307087045579, 371285306993778751, 371285306939053702, 371285306830295878, 371285306870565435, 371285306884472722, 371285306887084163]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493759570741403, 362493839822424352⟩, ⟨(-630278623043209112), (-626300616601224164)⟩, true⟩

def words09 : List Nat := [371285306880027054, 371285306961209557, 371285307173132875, 371285307175654634, 371285307140545480, 371285307054175409, 371285307014871902, 371285307017664039, 371285307113616425, 371285307232723923]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk733B

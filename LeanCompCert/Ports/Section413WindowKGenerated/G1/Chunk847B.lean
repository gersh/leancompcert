import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk847A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk847B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk847A

def state06 : KState := ⟨⟨362477477990965871, 362477586199959387⟩, ⟨648937237035465377, 655130194684666047⟩, true⟩

def words05 : List Nat := [371285315267534860, 371285315417367687, 371285315564891129, 371285315567836926, 371285315557788553, 371285315533170296, 371285315606476576, 371285315609420332, 371285315525584982, 371285315437744719]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488509269722077, 362488617505101854⟩, ⟨(-286107346363610081), (-279912152079050293)⟩, true⟩

def words06 : List Nat := [371285315396484067, 371285315399767648, 371285315446470387, 371285315500733275, 371285315531418803, 371285315534382763, 371285315439850175, 371285315415141557, 371285315482982868, 371285315525036985]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488373858299607, 362488482120475748⟩, ⟨(-274613192641757890), (-268415726693375180)⟩, true⟩

def words07 : List Nat := [371285315566293148, 371285315608495441, 371285315741851570, 371285315813014133, 371285315924159779, 371285316036454760, 371285316098445525, 371285316101400789, 371285316090323378, 371285316131319058]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485593723296713, 362485702011697844⟩, ⟨(-38895541261184780), (-32695851822446484)⟩, true⟩

def words08 : List Nat := [371285316290750715, 371285316293695246, 371285316267919944, 371285316234536862, 371285316199933045, 371285316199277826, 371285316227810659, 371285316313782010, 371285316398885232, 371285316406482404]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492268349137722, 362492376664238711⟩, ⟨(-604862757336256370), (-598660803884396710)⟩, true⟩

def words09 : List Nat := [371285316470577606, 371285316536190061, 371285316739249760, 371285316757891428, 371285316760170435, 371285316756439306, 371285316847256949, 371285316896317532, 371285316981590122, 371285317068197575]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk847B

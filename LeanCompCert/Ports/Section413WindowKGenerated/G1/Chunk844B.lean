import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk844A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk844B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk844A

def state06 : KState := ⟨⟨362477706874226679, 362477814289188716⟩, ⟨627546346929102067, 633672121428960227⟩, true⟩

def words05 : List Nat := [371285317140360312, 371285317230900057, 371285317320412636, 371285317323344604, 371285317225904202, 371285317132217286, 371285317079797806, 371285317082749984, 371285317004652842, 371285316919089604]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480819826887827, 362480927268108499⟩, ⟨364666853152349348, 370794845594581958⟩, true⟩

def words06 : List Nat := [371285316832258558, 371285316820552864, 371285316830055062, 371285316907091758, 371285316961269728, 371285316964202301, 371285316865577975, 371285316888806160, 371285316928214369, 371285316931250379]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478673992857124, 362478781460857073⟩, ⟨545956644251305944, 552086898865248252⟩, true⟩

def words07 : List Nat := [371285316881477058, 371285316820117405, 371285316781322227, 371285316784607145, 371285316791404858, 371285316815392167, 371285316826739309, 371285316829672116, 371285316654052665, 371285316580398566]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472192269407547, 362472299763532259⟩, ⟨1093576149436374327, 1099708611207156209⟩, true⟩

def words08 : List Nat := [371285316567746850, 371285316570680489, 371285316469696802, 371285316336406836, 371285316202023329, 371285316101945858, 371285315930693506, 371285315823185133, 371285315714661696, 371285315606959969]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481573126303900, 362481680646898644⟩, ⟨300926515426986361, 307061213786372291⟩, true⟩

def words09 : List Nat := [371285315454912828, 371285315376283966, 371285315317206355, 371285315320140143, 371285315174583494, 371285315006899536, 371285314838021694, 371285314728167594, 371285314547133459, 371285314507416826]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk844B

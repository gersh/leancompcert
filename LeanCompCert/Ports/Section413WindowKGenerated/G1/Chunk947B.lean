import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk947A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk947B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk947A

def state06 : KState := ⟨⟨362495049439634858, 362495185857828185⟩, ⟨(-956321730714563271), (-947593888114116489)⟩, true⟩

def words05 : List Nat := [371285185237175296, 371285185309445446, 371285185461485845, 371285185532706388, 371285185586169007, 371285185640634846, 371285185747694867, 371285185810739367, 371285185918560137, 371285186027854735]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489753405060862, 362489889853224298⟩, ⟨(-454484254961524972), (-445753572243188350)⟩, true⟩

def words06 : List Nat := [371285186136331426, 371285186139651786, 371285186162464811, 371285186229440408, 371285186300886277, 371285186304265808, 371285186284177743, 371285186266611863, 371285186319017663, 371285186372494506]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481033096610853, 362481169574670472⟩, ⟨372025126966501433, 380758643098871589⟩, true⟩

def words07 : List Nat := [371285186535789545, 371285186700415850, 371285186842422393, 371285186845743166, 371285186839151961, 371285186837318178, 371285186939242077, 371285186942562890, 371285186902204068, 371285186863582678]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481088264680272, 362481224772433289⟩, ⟨366830219016577103, 375566549645484203⟩, true⟩

def words08 : List Nat := [371285186892458969, 371285186909641657, 371285186972602312, 371285187036947916, 371285187078745837, 371285187082067353, 371285186988824382, 371285186910454164, 371285186859401436, 371285186862839930]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492175877257005, 362492312415321523⟩, ⟨(-684218706645223508), (-675479502643004420)⟩, true⟩

def words09 : List Nat := [371285186823529139, 371285186783101440, 371285186808587907, 371285186841636803, 371285186906870686, 371285186973363486, 371285187037736216, 371285187041083399, 371285187099944447, 371285187179272927]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk947B

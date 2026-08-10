import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk783A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk783B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk783A

def state06 : KState := ⟨⟨362488349902613371, 362488441831025467⟩, ⟨(-255535837867984969), (-250671461575002341)⟩, true⟩

def words05 : List Nat := [371285242920441820, 371285242919672456, 371285242950570648, 371285242953581203, 371285242907789207, 371285242911880823, 371285242915053116, 371285242917806936, 371285242855450634, 371285242899649209]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481027241430543, 362481119193922914⟩, ⟨318300786545481251, 323167049892166681⟩, true⟩

def words06 : List Nat := [371285243057731522, 371285243060435832, 371285243001741747, 371285242943384472, 371285242884016744, 371285242832163951, 371285242735629192, 371285242770783991, 371285242797723504, 371285242800531211]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493135210202862, 362493227187142706⟩, ⟨(-630627307071374558), (-625759127653086104)⟩, true⟩

def words07 : List Nat := [371285242846854593, 371285242947251202, 371285243197381193, 371285243246151472, 371285243256394595, 371285243267482816, 371285243384978877, 371285243422228965, 371285243525955419, 371285243630826085]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489413725897642, 362489505727278788⟩, ⟨(-338968850600001285), (-334098755350751517)⟩, true⟩

def words08 : List Nat := [371285243735881569, 371285243738586663, 371285243657222174, 371285243691153291, 371285243759313095, 371285243762084187, 371285243740121135, 371285243688744202, 371285243716808609, 371285243774307775]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479512992928349, 362479605018720016⟩, ⟨437264048367558001, 442136057277655521⟩, true⟩

def words09 : List Nat := [371285243984143112, 371285244195099654, 371285244373563777, 371285244384014948, 371285244443669537, 371285244504632452, 371285244648269304, 371285244650975058, 371285244578041490, 371285244509246517]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk783B

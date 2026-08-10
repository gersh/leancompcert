import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk580A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk580B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk580A

def state06 : KState := ⟨⟨360567469214150089, 360567490619257554⟩, ⟨838063412982695157, 838903042094147729⟩, true⟩

def words05 : List Nat := [360581942250024837, 360581942246606212, 360581942243098542, 360581942048018677, 360581941556758592, 360581940894317452, 360581940231660938, 360581939865951809, 360581939765701308, 360581939517674608]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594653778440767, 360594675191192852⟩, ⟨(-740342695710098639), (-739502622713450217)⟩, true⟩

def words06 : List Nat := [360581939317338619, 360581939514481037, 360581939889168725, 360581940264000029, 360581940364085169, 360581940364895894, 360581940269004082, 360581940369958586, 360581940514570791, 360581940734704873]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577604481718296, 360577625902202003⟩, ⟨249849946731343032, 250690468741657682⟩, true⟩

def words07 : List Nat := [360581940767249012, 360581940799893590, 360581941128965455, 360581941606528880, 360581941902234305, 360581942198060046, 360581942336158206, 360581942336969159, 360581942271538253, 360581942198151412]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582910229518510, 360582931657635191⟩, ⟨(-58355454169642614), (-57514488798516658)⟩, true⟩

def words08 : List Nat := [360581942317262656, 360581942318073577, 360581942284643968, 360581942071827496, 360581941858882253, 360581941570462120, 360581941602875800, 360581941698411063, 360581941699135575, 360581941581912644]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583366306703961, 360583387742484608⟩, ⟨(-84961465662824329), (-84120055054226781)⟩, true⟩

def words09 : List Nat := [360581941643600172, 360581941705519357, 360581941706186739, 360581941686869848, 360581941493940261, 360581941047528189, 360581940600979617, 360581940137990991, 360581939892144859, 360581939917919554]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk580B

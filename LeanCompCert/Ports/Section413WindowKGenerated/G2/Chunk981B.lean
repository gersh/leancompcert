import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk981A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk981B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk981A

def state06 : KState := ⟨⟨360591448639383284, 360591512402737989⟩, ⟨(-893712545120421143), (-889486249468530671)⟩, true⟩

def words05 : List Nat := [360582450224603783, 360582450257150427, 360582450305291927, 360582450445953826, 360582450547157886, 360582450648592799, 360582450697849470, 360582450711784872, 360582450805252887, 360582450899193114]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576832037683856, 360576895814480085⟩, ⟨541059957598754900, 545287572738762800⟩, true⟩

def words06 : List Nat := [360582450962255987, 360582450963681865, 360582450923389567, 360582450817112633, 360582450710594372, 360582450559023195, 360582450458797124, 360582450438937706, 360582450418898658, 360582450337987662]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591403521685713, 360591467311943836⟩, ⟨(-889531520161402416), (-885302583402922214)⟩, true⟩

def words07 : List Nat := [360582450308864325, 360582450336755891, 360582450409820735, 360582450411246830, 360582450403116091, 360582450278478437, 360582450153563731, 360582450091567191, 360582450172726538, 360582450266044906]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585159211649901, 360585223015515351⟩, ⟨(-276450364462389697), (-272220091668078061)⟩, true⟩

def words08 : List Nat := [360582450307250467, 360582450350738505, 360582450464908436, 360582450579494658, 360582450652941885, 360582450710713874, 360582450711986216, 360582450702240915, 360582450692248345, 360582450662736909]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565374676146031, 360565438493440246⟩, ⟨1666345947318853151, 1670577538749686827⟩, true⟩

def words09 : List Nat := [360582450775439686, 360582450888420575, 360582450941320742, 360582450942748315, 360582450939403960, 360582450887852182, 360582450835862660, 360582450776380399, 360582450656431399, 360582450484669877]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk981B

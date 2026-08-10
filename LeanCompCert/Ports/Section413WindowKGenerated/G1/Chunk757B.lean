import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk757A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk757B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk757A

def state06 : KState := ⟨⟨362474016376045005, 362474102081389629⟩, ⟨837451926813966054, 841836704014049378⟩, true⟩

def words05 : List Nat := [371285213856289381, 371285213988795488, 371285214117411530, 371285214120066047, 371285214135580813, 371285214168891451, 371285214256160958, 371285214258769385, 371285214114010461, 371285213970302170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481129206104136, 362481214934846184⟩, ⟨298571155744585298, 302957705646786368⟩, true⟩

def words06 : List Nat := [371285213825432165, 371285213742313191, 371285213594583716, 371285213602276963, 371285213604295427, 371285213584183888, 371285213359554905, 371285213310483219, 371285213318124789, 371285213320825421]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476273743965136, 362476359496455985⟩, ⟨666543479186926739, 670931828656255585⟩, true⟩

def words07 : List Nat := [371285213270024328, 371285213219169397, 371285213287678087, 371285213336767291, 371285213391748799, 371285213447733621, 371285213483442580, 371285213486051731, 371285213289507801, 371285213175905131]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482514989470957, 362482600765226044⟩, ⟨193573417132987170, 197963529687925118⟩, true⟩

def words08 : List Nat := [371285213118045014, 371285213120699750, 371285213035173368, 371285212950587395, 371285212864983274, 371285212805246862, 371285212714480849, 371285212758027024, 371285212763148172, 371285212765881645]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504388089916372, 362504473889265538⟩, ⟨(-1464305308766526698), (-1459913407894945060)⟩, true⟩

def words09 : List Nat := [371285212827083721, 371285212924131396, 371285213193772648, 371285213232265971, 371285213248221983, 371285213265014360, 371285213454683780, 371285213559097384, 371285213814961514, 371285214072008577]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk757B

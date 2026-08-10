import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk931A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk931B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk931A

def state06 : KState := ⟨⟨362481392378341901, 362481524055035826⟩, ⟨328288460409211311, 336570779747258473⟩, true⟩

def words05 : List Nat := [371285136568763679, 371285136688984298, 371285136807731270, 371285136810991909, 371285136809582587, 371285136825487472, 371285136923700958, 371285136926976411, 371285136915143885, 371285136880065316]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492716268605658, 362492847974506597⟩, ⟨(-726712061537687983), (-718427021123885319)⟩, true⟩

def words06 : List Nat := [371285136899063495, 371285136902656258, 371285136949137632, 371285136998733220, 371285137029161841, 371285137032423661, 371285136929266350, 371285136931205076, 371285137044558563, 371285137130777069]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491442449290963, 362491574184811664⟩, ⟨(-608008393439411820), (-599720593199291558)⟩, true⟩

def words07 : List Nat := [371285137215444318, 371285137301170155, 371285137468379204, 371285137586408488, 371285137738080384, 371285137891032719, 371285138000936877, 371285138004197262, 371285138029346883, 371285138102421485]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483482554970717, 362483614319533368⟩, ⟨133721830374761831, 142012336891262841⟩, true⟩

def words08 : List Nat := [371285138218441053, 371285138221701620, 371285138184417232, 371285138143261926, 371285138100730830, 371285138094704904, 371285138096651091, 371285138157621810, 371285138217186630, 371285138220562355]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496808477070999, 362496940271194215⟩, ⟨(-1108209586829120244), (-1099916325418132590)⟩, true⟩

def words09 : List Nat := [371285138238036160, 371285138273570760, 371285138394535428, 371285138398719831, 371285138401272345, 371285138397992667, 371285138446204388, 371285138461330522, 371285138590170416, 371285138720508942]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk931B

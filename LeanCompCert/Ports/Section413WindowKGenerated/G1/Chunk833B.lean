import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk833A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk833B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk833A

def state06 : KState := ⟨⟨362492728569628019, 362492833099323605⟩, ⟨(-632293683469493292), (-626410015611458558)⟩, true⟩

def words05 : List Nat := [371285318753015538, 371285318758524961, 371285318832903995, 371285318835795498, 371285318737385230, 371285318616776618, 371285318515096450, 371285318518334498, 371285318580490626, 371285318673925500]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469171538705508, 362469276094497374⟩, ⟨1331511213101973256, 1337397056480703940⟩, true⟩

def words06 : List Nat := [371285318753441214, 371285318756332595, 371285318643877672, 371285318592081677, 371285318538888089, 371285318530534344, 371285318350145157, 371285318155807208, 371285317960285850, 371285317800824359]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362454185053404180, 362454289635199812⟩, ⟨2581069682307099277, 2586957693750747519⟩, true⟩

def words07 : List Nat := [371285317610372115, 371285317553597343, 371285317495866805, 371285317438676267, 371285317188894691, 371285316942652270, 371285316694875589, 371285316491537528, 371285316121764442, 371285315752898910]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471276143144869, 362471380750795123⟩, ⟨1155960878640389255, 1161851045976437403⟩, true⟩

def words08 : List Nat := [371285315382759784, 371285315149750983, 371285314861317932, 371285314717976851, 371285314573685048, 371285314396901566, 371285314042714003, 371285313810863309, 371285313577549470, 371285313489084804]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479748286373336, 362479852920448709⟩, ⟨449397841251446221, 455290212306663329⟩, true⟩

def words09 : List Nat := [371285313324227396, 371285313112445566, 371285312899449862, 371285312812834784, 371285312665770108, 371285312545880933, 371285312425043934, 371285312304819954, 371285312097546924, 371285312035704185]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk833B

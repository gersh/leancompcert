import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk733A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk733B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk733A

def state06 : KState := ⟨⟨360559710488399650, 360559745303442439⟩, ⟨1663362558228536923, 1665087649370348035⟩, true⟩

def words05 : List Nat := [360582443380753993, 360582443630907698, 360582443738269708, 360582443739312183, 360582443661062177, 360582443472928307, 360582443284493885, 360582443249021973, 360582443098788921, 360582442790484020]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591088864332830, 360591123689208100⟩, ⟨(-638708473602737995), (-636982661101033179)⟩, true⟩

def words06 : List Nat := [360582442481932594, 360582442359177856, 360582442484943928, 360582442641182907, 360582442642144934, 360582442634424105, 360582442441048313, 360582442199971639, 360582441958585035, 360582442021231638]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599912785930923, 360599947620732530⟩, ⟨(-1286187948898678343), (-1284461408052406669)⟩, true⟩

def words07 : List Nat := [360582442022795598, 360582442024480517, 360582442175811337, 360582442469333193, 360582442708801216, 360582442948431603, 360582443082195532, 360582443136381204, 360582443375770169, 360582443615498854]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581772844614872, 360581807689251163⟩, ⟨44895718015160008, 46622980579784768⟩, true⟩

def words08 : List Nat := [360582443757268863, 360582443758311800, 360582443714753919, 360582443561221974, 360582443407528479, 360582443154208802, 360582443032273579, 360582443064638157, 360582443065570174, 360582442966272281]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593561677250262, 360593596531732506⟩, ⟨(-820374314855309857), (-818646329648089395)⟩, true⟩

def words09 : List Nat := [360582443087922386, 360582443218538657, 360582443435224437, 360582443466755290, 360582443467743432, 360582443319979396, 360582443172021377, 360582443158103815, 360582443310901406, 360582443463931685]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk733B

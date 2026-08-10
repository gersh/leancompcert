import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk848A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk848B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk848A

def state06 : KState := ⟨⟨360610530479147296, 360610577599073347⟩, ⟨(-2389173462627436741), (-2386473096034158905)⟩, true⟩

def words05 : List Nat := [360582454640463367, 360582454528584983, 360582454416338961, 360582454503556905, 360582454504681067, 360582454490014920, 360582454597981316, 360582454791984636, 360582455124372379, 360582455457028896]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599934387406296, 360599981518971619⟩, ⟨(-1490063396916826699), (-1487362042559091583)⟩, true⟩

def words06 : List Nat := [360582455682526201, 360582455799831434, 360582456030726861, 360582456261984929, 360582456401994261, 360582456403436800, 360582456404522866, 360582456336399903, 360582456337377198, 360582456545275550]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577958267718426, 360578005410757918⟩, ⟨375205780423196664, 377908108651765004⟩, true⟩

def words07 : List Nat := [360582456891459245, 360582457237868575, 360582457499536480, 360582457622593038, 360582457636551142, 360582457650822254, 360582457705999690, 360582457724150634, 360582457725247012, 360582457674054947]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581908354299561, 360581955508866726⟩, ⟨39947511693044485, 42650818446645923⟩, true⟩

def words08 : List Nat := [360582457622590195, 360582457729140062, 360582457917013376, 360582458105115169, 360582458174990126, 360582458176209521, 360582458107251551, 360582458060285601, 360582458012966005, 360582457933397845]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591737224146678, 360591784390321423⟩, ⟨(-794518398854350181), (-791814106675078663)⟩, true⟩

def words09 : List Nat := [360582457928565742, 360582457854308934, 360582457779818933, 360582457830539211, 360582457856135402, 360582457881951319, 360582457883047938, 360582457845737463, 360582457956576647, 360582458067820215]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk848B

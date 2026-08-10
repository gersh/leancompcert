import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk302A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk302B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk302A

def state06 : KState := ⟨⟨360649048142800898, 360649053654220493⟩, ⟨(-1985469711593535902), (-1985356924872602624)⟩, true⟩

def words05 : List Nat := [360583440846684404, 360583440283592313, 360583440246209528, 360583440805266219, 360583440805636223, 360583440430579798, 360583440460625237, 360583441540558407, 360583443709161857, 360583445877713683]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619344096035942, 360619349611284415⟩, ⟨(-1086865033794879743), (-1086752131193366711)⟩, true⟩

def words06 : List Nat := [360583447026807740, 360583447089791149, 360583447874189376, 360583448658655100, 360583449165705838, 360583449166107634, 360583449084297877, 360583448246083021, 360583447657368244, 360583448843843850]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360522262996799913, 360522268515829006⟩, ⟨1852511517727309457, 1852624534787418213⟩, true⟩

def words07 : List Nat := [360583451118078966, 360583453392243357, 360583455121245782, 360583455764874446, 360583455765216822, 360583455638313415, 360583455511299022, 360583455120673350, 360583453644869009, 360583451624639687]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575417601685521, 360575423124511342⟩, ⟨242798359623125162, 242911491666680130⟩, true⟩

def words08 : List Nat := [360583449604453223, 360583448427663795, 360583448118891085, 360583447978064734, 360583447837219647, 360583446781505837, 360583445275297357, 360583444409942611, 360583443544533218, 360583442652133220]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572670298562440, 360572675825214481⟩, ⟨326093568045873796, 326206816004082682⟩, true⟩

def words09 : List Nat := [360583442387742277, 360583441419192318, 360583440568005186, 360583441664492241, 360583442311506222, 360583442958549815, 360583443061815241, 360583443062217224, 360583442081596260, 360583441726732768]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk302B

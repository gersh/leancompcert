import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk901A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk901B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk901A

def state06 : KState := ⟨⟨360576459955879557, 360576513395334969⟩, ⟨489667596579506613, 492921166908769489⟩, true⟩

def words05 : List Nat := [360581979863048515, 360581980180562794, 360581980400996335, 360581980498658024, 360581980507350850, 360581980516390776, 360581980618528795, 360581980635861131, 360581980637020711, 360581980577754100]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584196774703374, 360584250226434471⟩, ⟨(-207888463722127876), (-204633786555710982)⟩, true⟩

def words06 : List Nat := [360581980524063359, 360581980593247426, 360581980784935021, 360581980976867844, 360581981064225507, 360581981065526658, 360581981029916268, 360581980930848306, 360581980831390049, 360581980829549046]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593859683713811, 360593913147844531⟩, ⟨(-1079249593897478900), (-1075993798597525468)⟩, true⟩

def words07 : List Nat := [360581980830719686, 360581980781924660, 360581980805664725, 360581980976381668, 360581981115190176, 360581981254206781, 360581981331331905, 360581981389577146, 360581981522940210, 360581981656747765]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581236957514053, 360581290433913830⟩, ⟨59053944067766673, 62310845853647603⟩, true⟩

def words08 : List Nat := [360581981738902245, 360581981740203856, 360581981735370092, 360581981652890008, 360581981570202318, 360581981415763663, 360581981351414673, 360581981381460680, 360581981382639016, 360581981318112230]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360606897928597604, 360606951417280685⟩, ⟨(-2255479292354204155), (-2252221282675307103)⟩, true⟩

def words09 : List Nat := [360581981426679456, 360581981543286880, 360581981666365028, 360581981754115373, 360581981755336744, 360581981726056716, 360581981788770340, 360581981944225043, 360581982222100571, 360581982500276713]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk901B

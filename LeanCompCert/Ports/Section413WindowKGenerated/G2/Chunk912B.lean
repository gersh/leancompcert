import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk912A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk912B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk912A

def state06 : KState := ⟨⟨360592278247291419, 360592333050370310⟩, ⟨(-947911328621555315), (-944534062388823227)⟩, true⟩

def words05 : List Nat := [360581981467856681, 360581981581298471, 360581981814406055, 360581982124907322, 360581982404988257, 360581982685291046, 360581982892981912, 360581983010366208, 360581983124863382, 360581983239800748]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589425730346031, 360589480545834126⟩, ⟨(-687593148187225511), (-684214749427371263)⟩, true⟩

def words06 : List Nat := [360581983451841648, 360581983544243286, 360581983563244714, 360581983582391517, 360581983583495147, 360581983665741072, 360581983778238770, 360581983890979610, 360581983943730000, 360581984027230985]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595780382266027, 360595835210225703⟩, ⟨(-1267671175370987780), (-1264291638269721478)⟩, true⟩

def words07 : List Nat := [360581984205590412, 360581984384333383, 360581984470774791, 360581984477204720, 360581984478422636, 360581984382262381, 360581984285848641, 360581984358852861, 360581984511659863, 360581984664786130]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584295753571213, 360584350594086815⟩, ⟨(-219355891216471758), (-215975207948841976)⟩, true⟩

def words08 : List Nat := [360581984757517480, 360581984758836558, 360581984823205313, 360581984916232680, 360581984978909381, 360581985007039766, 360581985008249985, 360581984938117852, 360581984867742120, 360581984805477327]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579440646746946, 360579495499684880⟩, ⟨223954444203702155, 227336261568840543⟩, true⟩

def words09 : List Nat := [360581984952288062, 360581985099349694, 360581985186105256, 360581985276060217, 360581985299301359, 360581985322902360, 360581985465916475, 360581985516312120, 360581985517493021, 360581985491596916]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk912B

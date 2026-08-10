import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk788A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk788B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk788A

def state06 : KState := ⟨⟨360592057072609354, 360592097533643572⟩, ⟨(-780893242104762583), (-778738233936819623)⟩, true⟩

def words05 : List Nat := [360582222346356345, 360582222337613273, 360582222479136958, 360582222511508696, 360582222512565780, 360582222393331518, 360582222314096420, 360582222460434055, 360582222586574029, 360582222712959878]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580309935132730, 360580350406909099⟩, ⟨145513407116672400, 147669262462954084⟩, true⟩

def words06 : List Nat := [360582222740117455, 360582222815796099, 360582222945684419, 360582223075898927, 360582223165785790, 360582223166912843, 360582223150059940, 360582223025516203, 360582222900777773, 360582222719099577]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556933890896653, 360556974373278409⟩, ⟨1989326089974126907, 1991482781821083409⟩, true⟩

def words07 : List Nat := [360582222720296008, 360582222745442236, 360582222746446422, 360582222675262423, 360582222479058322, 360582222240550439, 360582222001684459, 360582221923531641, 360582221684850240, 360582221365948555]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570216861928946, 360570257354962910⟩, ⟨941385490348898640, 943543022493246724⟩, true⟩

def words08 : List Nat := [360582221046801673, 360582220700206808, 360582220433691707, 360582220124315065, 360582219814862066, 360582219370054562, 360582218764665232, 360582218320083475, 360582217875179514, 360582217591019359]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567434416091058, 360567474919856294⟩, ⟨1160921137450929929, 1163079516237292683⟩, true⟩

def words09 : List Nat := [360582217440418985, 360582217209592804, 360582216978548940, 360582216917511298, 360582216918455322, 360582216862143235, 360582216805734900, 360582216607584747, 360582216290655375, 360582216105106450]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk788B

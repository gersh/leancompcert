import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk619A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk619B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk619A

def state06 : KState := ⟨⟨360556642967405697, 360556667470944728⟩, ⟨1607034632651570506, 1608060268756471258⟩, true⟩

def words05 : List Nat := [360582621274262524, 360582621622388585, 360582621828058011, 360582621828927057, 360582621775028705, 360582621654857971, 360582621534439839, 360582621349989898, 360582621088869719, 360582620670892380]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578586862534662, 360578611374272019⟩, ⟨247295737985337058, 248321882099174054⟩, true⟩

def words06 : List Nat := [360582620252731583, 360582620104587279, 360582620105295025, 360582620070472203, 360582620035578033, 360582619749849004, 360582619204535623, 360582618919786312, 360582618634791832, 360582618504852932]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590436666278572, 360590461186307455⟩, ⟨(-487187072963015125), (-486160414983103411)⟩, true⟩

def words07 : List Nat := [360582618440983090, 360582618155693917, 360582617870248064, 360582617777729504, 360582617778458404, 360582617686649958, 360582617594749430, 360582617364406223, 360582617358033285, 360582617485576859]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360594293879915771, 360594318408126506⟩, ⟨(-726278343960180540), (-725251178827602576)⟩, true⟩

def words08 : List Nat := [360582617873003427, 360582618174115587, 360582618301466191, 360582618428904507, 360582618429651084, 360582618294805665, 360582618542604711, 360582618797081019, 360582618920553975, 360582619110182811]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594583905229038, 360594608441663272⟩, ⟨(-744175369211099132), (-743147694263999018)⟩, true⟩

def words09 : List Nat := [360582619559710643, 360582620009506027, 360582620636254593, 360582621073098804, 360582621290031731, 360582621507031414, 360582621685605500, 360582621993580870, 360582622187627984, 360582622381853528]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk619B

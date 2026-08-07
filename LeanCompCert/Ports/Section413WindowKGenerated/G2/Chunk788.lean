import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk788

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572911418340670, 360572951815430673⟩, ⟨728533414876451515, 730683382326891149⟩, true⟩

def state01 : KState := ⟨⟨360595913449480815, 360595953857288825⟩, ⟨(-1084256774043412188), (-1082105961961847936)⟩, true⟩

def words00 : List Nat := [360582224330517619, 360582224133449172, 360582223890071466, 360582223807840706, 360582223725293677, 360582223602844189, 360582223548735120, 360582223409110313, 360582223289299521, 360582223464806027]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565886808850810, 360565927227278414⟩, ⟨1282350495382607726, 1284502144446015478⟩, true⟩

def words01 : List Nat := [360582223750941728, 360582224037291312, 360582224199711928, 360582224240669384, 360582224241618055, 360582224175813263, 360582224176748658, 360582224177874614, 360582224085281830, 360582223879707316]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585783879361124, 360585824308410144⟩, ⟨(-285999891913246758), (-283847405616630306)⟩, true⟩

def words02 : List Nat := [360582223673863832, 360582223524691607, 360582223593463075, 360582223708872024, 360582223709911851, 360582223689840285, 360582223645305218, 360582223597132079, 360582223553652930, 360582223600495534]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582801862621400, 360582842302404371⟩, ⟨(-50912495309129213), (-48759162801795753)⟩, true⟩

def words03 : List Nat := [360582223601510509, 360582223551148215, 360582223546217560, 360582223717025270, 360582223847449567, 360582223978054230, 360582223986856135, 360582223987982366, 360582223843942420, 360582223853084832]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574459924687327, 360574500375094861⟩, ⟨606730913869640842, 608885084070371100⟩, true⟩

def words04 : List Nat := [360582223857142184, 360582223858268552, 360582223744430773, 360582223529722059, 360582223314838052, 360582223010904427, 360582222819051578, 360582222720876740, 360582222622563710, 360582222443377301]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk788

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk992A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk992B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk992A

def state06 : KState := ⟨⟨360596313449973200, 360596378706318185⟩, ⟨(-1389062377392521033), (-1384688707146278133)⟩, true⟩

def words05 : List Nat := [360582428519615157, 360582428638408280, 360582428704189500, 360582428705632413, 360582428670346370, 360582428548473458, 360582428426323199, 360582428445145028, 360582428586853953, 360582428728913704]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581194434561209, 360581259704660375⟩, ⟨111645660032676166, 116020695585878168⟩, true⟩

def words06 : List Nat := [360582428805804031, 360582428821612881, 360582428871795612, 360582428922409438, 360582428946911895, 360582428948355000, 360582428871771709, 360582428705471623, 360582428538889318, 360582428443409100]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569678244344527, 360569743528026218⟩, ⟨1254958067953800123, 1259334451913514045⟩, true⟩

def words07 : List Nat := [360582428479888129, 360582428528415550, 360582428529701159, 360582428528471050, 360582428529691038, 360582428454185044, 360582428402575194, 360582428404018468, 360582428328468934, 360582428202199401]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587086667656413, 360587151964977371⟩, ⟨(-473488935375758551), (-469111197239961961)⟩, true⟩

def words08 : List Nat := [360582428075626691, 360582427908011459, 360582427790596642, 360582427749714833, 360582427708721552, 360582427581696617, 360582427438860431, 360582427361624643, 360582427306445679, 360582427355523947]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578113000465711, 360578178311531839⟩, ⟨417553494068823075, 421932597027897365⟩, true⟩

def words09 : List Nat := [360582427356811616, 360582427340347638, 360582427366854965, 360582427487703576, 360582427539325862, 360582427591163061, 360582427592473707, 360582427546596702, 360582427422130070, 360582427380988314]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk992B

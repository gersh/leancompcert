import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk807A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk807B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk807A

def state06 : KState := ⟨⟨362477876872675949, 362477974744723223⟩, ⟨574368292618873072, 579705583671251812⟩, true⟩

def words05 : List Nat := [371285152936102893, 371285152905466604, 371285152948624609, 371285152958043686, 371285153005166772, 371285153053346383, 371285153098999702, 371285153101793464, 371285152957703681, 371285152872307068]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477819279441080, 362477917176386870⟩, ⟨579056245946954957, 584395547932391715⟩, true⟩

def words06 : List Nat := [371285152849669423, 371285152852482193, 371285152781567266, 371285152711631024, 371285152640652846, 371285152595260068, 371285152493341753, 371285152489376270, 371285152484441804, 371285152480929800]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486998709282334, 362487096631459819⟩, ⟨(-162451999555223513), (-157110659476081431)⟩, true⟩

def words07 : List Nat := [371285152401077782, 371285152412221543, 371285152440094558, 371285152442888921, 371285152266783283, 371285152064224654, 371285151860504397, 371285151811139009, 371285151708021546, 371285151735265466]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483565428347529, 362483663375749895⟩, ⟨114878427232087854, 120221805098999394⟩, true⟩

def words08 : List Nat := [371285151761492924, 371285151764300995, 371285151681575277, 371285151719289813, 371285151790223058, 371285151793019916, 371285151691781790, 371285151561635053, 371285151450357118, 371285151453545402]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481362667838864, 362481460640421499⟩, ⟨292913718727922380, 298259131037044648⟩, true⟩

def words09 : List Nat := [371285151561271405, 371285151688575703, 371285151810833065, 371285151834344173, 371285151859596859, 371285151886178137, 371285152038500241, 371285152041295950, 371285152008800656, 371285151966300671]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk807B

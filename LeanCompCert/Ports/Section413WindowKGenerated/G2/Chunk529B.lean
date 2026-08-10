import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk529A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk529B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk529A

def state06 : KState := ⟨⟨360555532358931277, 360555550036967124⟩, ⟨1398144876704602739, 1398777459965708315⟩, true⟩

def words05 : List Nat := [360581963185261659, 360581963349563754, 360581963350219110, 360581963332595061, 360581963333221909, 360581963035043372, 360581962793503650, 360581962794237939, 360581962496033835, 360581961998069196]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590383047863358, 360590400732839052⟩, ⟨(-447591815677781253), (-446958864848716251)⟩, true⟩

def words06 : List Nat := [360581961499957101, 360581961382126662, 360581961835950520, 360581962289897899, 360581962396433296, 360581962397167813, 360581962481008223, 360581962701290862, 360581962769744590, 360581962929798734]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581327467350372, 360581345159321304⟩, ⟨32166210744387671, 32799532145162637⟩, true⟩

def words07 : List Nat := [360581962930452970, 360581962912004496, 360581963229861531, 360581963748317720, 360581964054807310, 360581964361419545, 360581964489517950, 360581964490252444, 360581964262886381, 360581964252038276]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579708279995512, 360579725978891940⟩, ⟨117937048820678588, 118570737169560814⟩, true⟩

def words08 : List Nat := [360581964584779776, 360581964699355286, 360581964700027706, 360581964514143183, 360581964328145466, 360581964052921510, 360581963956638608, 360581963914914634, 360581963873110325, 360581963584801915]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360596905865622714, 360596923571448508⟩, ⟨(-793513711743391267), (-792879656172709147)⟩, true⟩

def words09 : List Nat := [360581963657905587, 360581963773453893, 360581964176124605, 360581964223735820, 360581964224413210, 360581963968095797, 360581963711657822, 360581963367313512, 360581963577174202, 360581963860194519]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk529B

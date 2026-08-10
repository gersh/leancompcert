import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk654A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk654B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk654A

def state06 : KState := ⟨⟨360573527339159493, 360573554809572793⟩, ⟨611506221698741675, 612720928902234439⟩, true⟩

def words05 : List Nat := [360582915527653459, 360582915560398801, 360582915593478488, 360582915743638917, 360582915744416390, 360582915720159640, 360582915695825127, 360582915492706468, 360582915185686775, 360582915043744841]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561036341112785, 360561063820209710⟩, ⟨1429185679739187397, 1430400955417679919⟩, true⟩

def words06 : List Nat := [360582914901506260, 360582914784956148, 360582914505218893, 360582914108797778, 360582913712222062, 360582913257338349, 360582912919211599, 360582912660448253, 360582912401587923, 360582912009539444]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585941902686126, 360585969390501893⟩, ⟨(-201614530378128105), (-200398683833978383)⟩, true⟩

def words07 : List Nat := [360582911676590771, 360582911297712044, 360582910918566817, 360582910732018596, 360582910443475454, 360582909940136432, 360582909436636512, 360582909071772973, 360582908933165776, 360582908980858883]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563266115964768, 360563293612565465⟩, ⟨1283156575170266593, 1284372996993493411⟩, true⟩

def words08 : List Nat := [360582908981686178, 360582908854698825, 360582908601738043, 360582908385544178, 360582908169113719, 360582907792207645, 360582907242254503, 360582906563620754, 360582905884831381, 360582905354770283]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555183048937681, 360555210554241470⟩, ⟨1812651034051165735, 1813868025883731125⟩, true⟩

def words09 : List Nat := [360582905056059587, 360582904931015018, 360582904805867011, 360582904536858579, 360582904353130886, 360582904111156047, 360582903868917914, 360582903859549022, 360582903617696256, 360582903195858016]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk654B

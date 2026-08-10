import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk635A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk635B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk635A

def state06 : KState := ⟨⟨360586094754248257, 360586120592046714⟩, ⟨(-218840528847418611), (-217731149791858589)⟩, true⟩

def words05 : List Nat := [360582696902507466, 360582696826229775, 360582696749705287, 360582696664632738, 360582696425792163, 360582695969783223, 360582695513621028, 360582695129721613, 360582694990888979, 360582695045724412]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563859868544859, 360563885714846086⟩, ⟨1194421531928405697, 1195531451462655101⟩, true⟩

def words06 : List Nat := [360582695046520357, 360582694976758916, 360582694738767410, 360582694585038785, 360582694431078319, 360582694214805098, 360582693859249210, 360582693310364575, 360582692761330209, 360582692250184495]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566272005110528, 360566297859824703⟩, ⟨1041143873915466719, 1042254328302454227⟩, true⟩

def words07 : List Nat := [360582691955071813, 360582691853684484, 360582691752201576, 360582691526396062, 360582691393871717, 360582691197311334, 360582691050113170, 360582691051006906, 360582690918365084, 360582690661465195]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575830370964530, 360575856234117612⟩, ⟨433284211782021593, 434395202756836435⟩, true⟩

def words08 : List Nat := [360582690404375375, 360582690089508899, 360582689897817104, 360582689698802998, 360582689499734020, 360582689083478431, 360582688420721643, 360582688005371831, 360582687589755858, 360582687421454565]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360550066462752615, 360550092334418445⟩, ⟨2071716460247953971, 2072827992589630031⟩, true⟩

def words09 : List Nat := [360582687314832993, 360582686991329205, 360582686667665963, 360582686451474858, 360582686360158494, 360582686056160147, 360582685752072787, 360582685239718405, 360582684480956189, 360582683969522056]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk635B

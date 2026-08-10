import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk844A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk844B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk844A

def state06 : KState := ⟨⟨360573640947239076, 360573687606928460⟩, ⟨737004946644999669, 739666349565631765⟩, true⟩

def words05 : List Nat := [360582445370599002, 360582445547510947, 360582445654065220, 360582445655277804, 360582445621744916, 360582445475501845, 360582445328886786, 360582445322596159, 360582445302893124, 360582445200458719]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584447034790420, 360584493705937083⟩, ⟨(-175686729175614811), (-173024358514859473)⟩, true⟩

def words06 : List Nat := [360582445097755985, 360582445000311739, 360582445146274634, 360582445292466485, 360582445319467500, 360582445320680356, 360582445301291900, 360582445362473185, 360582445363477538, 360582445377415877]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360570367851525689, 360570414534229809⟩, ⟨1013665079711217467, 1016328426686517109⟩, true⟩

def words07 : List Nat := [360582445378497105, 360582445313967981, 360582445249210683, 360582445311027623, 360582445331057042, 360582445351303301, 360582445352384977, 360582445285297254, 360582445078021686, 360582444937007822]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570534115774420, 360570580809910286⟩, ⟨999584657454494234, 1002248970239380472⟩, true⟩

def words08 : List Nat := [360582444795584785, 360582444794415118, 360582444698708167, 360582444489894023, 360582444280887229, 360582444017064714, 360582443823125310, 360582443621594326, 360582443419935612, 360582443148296360]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575381664266955, 360575428369848747⟩, ⟨589934359243306265, 592599639151838139⟩, true⟩

def words09 : List Nat := [360582443008886105, 360582442891451188, 360582442773652414, 360582442717734353, 360582442555422071, 360582442267233966, 360582441978837353, 360582441687034041, 360582441465061375, 360582441383329834]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk844B

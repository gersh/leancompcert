import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk925A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk925B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk925A

def state06 : KState := ⟨⟨360570099110762579, 360570155548586745⟩, ⟨1092569854265166762, 1096097372573704960⟩, true⟩

def words05 : List Nat := [360581998025289565, 360581997995484098, 360581997965531324, 360581997877154590, 360581997851326340, 360581997783302210, 360581997761967287, 360581997763306218, 360581997695148940, 360581997568601587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589977521280767, 360590033971758921⟩, ⟨(-747516211283162150), (-743987521659601270)⟩, true⟩

def words06 : List Nat := [360581997441765655, 360581997311643644, 360581997259489164, 360581997280891062, 360581997282149498, 360581997177465867, 360581997002705895, 360581996944954418, 360581996944104382, 360581997032310718]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579822224828713, 360579878688051820⟩, ⟨192598740846044087, 196128610332983221⟩, true⟩

def words07 : List Nat := [360581997049401374, 360581997066637559, 360581997118642830, 360581997247210064, 360581997278306935, 360581997309608187, 360581997310801188, 360581997283524485, 360581997186511457, 360581997165156303]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587193706705396, 360587250182558307⟩, ⟨(-489835663469139824), (-486304624652037632)⟩, true⟩

def words08 : List Nat := [360581997237020479, 360581997383248439, 360581997466325118, 360581997549533853, 360581997603353832, 360581997731581553, 360581997832219818, 360581997933103094, 360581997944162460, 360581998002274565]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597108379595557, 360597164868093843⟩, ⟨(-1407863668447805923), (-1404331458733571685)⟩, true⟩

def words09 : List Nat := [360581998141868991, 360581998281867448, 360581998537973270, 360581998711965947, 360581998786669913, 360581998861499798, 360581998946897375, 360581999135328799, 360581999300196468, 360581999465358089]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk925B

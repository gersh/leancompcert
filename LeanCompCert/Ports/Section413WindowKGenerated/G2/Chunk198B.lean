import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk198A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk198B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk198A

def state06 : KState := ⟨⟨360507921989385940, 360507924277348352⟩, ⟨1483387901057691958, 1483418652733259560⟩, true⟩

def words05 : List Nat := [360582627111856089, 360582625380845214, 360582624443242105, 360582626496498190, 360582626597019098, 360582626697570198, 360582626697796750, 360582625529301087, 360582621827425477, 360582618066509141]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360537108514066435, 360537110804423835⟩, ⟨903508933948761913, 903539733200853191⟩, true⟩

def words06 : List Nat := [360582614305887766, 360582613067708181, 360582609296684791, 360582604238050723, 360582599179883551, 360582592824802502, 360582588981381055, 360582587659345662, 360582586337415645, 360582583362712756]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360521424099227430, 360521426391991888⟩, ⟨1215103792900396053, 1215134639992661907⟩, true⟩

def words07 : List Nat := [360582581074530840, 360582580252726682, 360582579430931896, 360582577411699611, 360582574380808826, 360582569163459629, 360582563946589106, 360582557793925990, 360582552939336588, 360582549864828542]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360472116205967999, 360472118501159342⟩, ⟨2195066513286318306, 2195097408636716628⟩, true⟩

def words08 : List Nat := [360582546790590805, 360582542285835788, 360582535254714328, 360582529782407040, 360582524310583142, 360582517386239100, 360582508977343175, 360582498599175744, 360582488222001593, 360582480361824839]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360420561384135988, 360420563681726048⟩, ⟨3221147491126581661, 3221178434199578979⟩, true⟩

def words09 : List Nat := [360582474813699603, 360582471781794376, 360582468750166583, 360582464128088756, 360582460246952403, 360582454951262440, 360582449656030513, 360582446128699964, 360582440078979418, 360582431944751153]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk198B

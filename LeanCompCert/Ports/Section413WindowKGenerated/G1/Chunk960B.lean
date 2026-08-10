import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk960A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk960B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk960A

def state06 : KState := ⟨⟨362494718973295510, 362494859308022409⟩, ⟨(-930577467169491884), (-921475941620017860)⟩, true⟩

def words05 : List Nat := [371285265773990116, 371285265814840944, 371285265962860741, 371285266072823962, 371285266213916707, 371285266356327917, 371285266494751880, 371285266498120321, 371285266591606467, 371285266695603009]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483871749846329, 362484012114636473⟩, ⟨111447291568142817, 120551705144045569⟩, true⟩

def words06 : List Nat := [371285266842648145, 371285266864676944, 371285266867212823, 371285266857020180, 371285266864124425, 371285266867875831, 371285266868349530, 371285266905134906, 371285266943078829, 371285266946583429]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502504667913874, 362502645063152492⟩, ⟨(-1678715771915495550), (-1669608432998950148)⟩, true⟩

def words07 : List Nat := [371285267000553311, 371285267069358540, 371285267237810036, 371285267312451003, 371285267357041202, 371285267402575787, 371285267526610250, 371285267602723295, 371285267785871940, 371285267970563958]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486030716259376, 362486171141916627⟩, ⟨(-95818454270818647), (-86708192574640509)⟩, true⟩

def words08 : List Nat := [371285268153484429, 371285268247297728, 371285268390181790, 371285268534807483, 371285268683703713, 371285268700933239, 371285268716858454, 371285268733952489, 371285268773699389, 371285268786934635]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483764336196085, 362483904792185801⟩, ⟨122015273735125127, 131128450224249791⟩, true⟩

def words09 : List Nat := [371285268898609699, 371285269011624511, 371285269123038515, 371285269126413211, 371285269144859141, 371285269173374911, 371285269308400445, 371285269311770328, 371285269302625046, 371285269292188135]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk960B

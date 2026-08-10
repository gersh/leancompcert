import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk954A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk954B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk954A

def state06 : KState := ⟨⟨362488182931246453, 362488321451509010⟩, ⟨(-304779877427125870), (-295852105841941146)⟩, true⟩

def words05 : List Nat := [371285221546070665, 371285221604768149, 371285221756439580, 371285221854628934, 371285221962784742, 371285222072269772, 371285222178100329, 371285222186695975, 371285222221481958, 371285222258059938]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486300296843108, 362486438846864335⟩, ⟨(-125028055395100168), (-116097442888309882)⟩, true⟩

def words06 : List Nat := [371285222402655037, 371285222415602529, 371285222428066094, 371285222441666826, 371285222479779546, 371285222483531938, 371285222587146760, 371285222696348452, 371285222781360435, 371285222797562576]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498744043785699, 362498882624170579⟩, ⟨(-1313110311606177332), (-1304176800141093922)⟩, true⟩

def words07 : List Nat := [371285222922415187, 371285223049119869, 371285223199721666, 371285223205066982, 371285223207665208, 371285223198524008, 371285223275907434, 371285223312826113, 371285223458154410, 371285223605097245]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482668297520585, 362482806908080323⟩, ⟨221872183227088221, 230808575943652667⟩, true⟩

def words08 : List Nat := [371285223747869910, 371285223751216713, 371285223851270284, 371285223959041365, 371285224088079338, 371285224091426282, 371285224074392808, 371285224037342054, 371285224001052041, 371285224004906626]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478425183066687, 362478563823718106⟩, ⟨627099626914553416, 636038893238049860⟩, true⟩

def words09 : List Nat := [371285224012332160, 371285224046386954, 371285224075241152, 371285224078654307, 371285224037306901, 371285224023884967, 371285224045212947, 371285224048576424, 371285223982846661, 371285223916841018]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk954B

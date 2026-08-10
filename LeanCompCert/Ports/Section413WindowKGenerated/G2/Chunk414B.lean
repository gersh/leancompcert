import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk414A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk414B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk414A

def state06 : KState := ⟨⟨360613738586856644, 360613749205837042⟩, ⟨(-1299098632261428692), (-1298801086463650708)⟩, true⟩

def words05 : List Nat := [360582414905588442, 360582415296018427, 360582416266814323, 360582417696956385, 360582418978848803, 360582420260771169, 360582421176487512, 360582421843090397, 360582422599153668, 360582423355363980]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608106831749576, 360608117456043654⟩, ⟨(-1065792572274179026), (-1065494806144540416)⟩, true⟩

def words06 : List Nat := [360582424098200001, 360582424262331788, 360582424262839927, 360582424014680783, 360582423766441719, 360582423370586016, 360582423739120095, 360582424213737809, 360582424308451934, 360582424928587250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360641081143710229, 360641091773319794⟩, ⟨(-2433445043575961581), (-2433147056986884929)⟩, true⟩

def words07 : List Nat := [360582426006906074, 360582427085344246, 360582428569634358, 360582429646868348, 360582430185643866, 360582430724427694, 360582431204377901, 360582432039474524, 360582433454099524, 360582434868785504]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360607703344397321, 360607713979384320⟩, ⟨(-1048878035196137165), (-1048579825523773487)⟩, true⟩

def words08 : List Nat := [360582435833658504, 360582436812193986, 360582437959023792, 360582439105961255, 360582440105106612, 360582440526284918, 360582440656853516, 360582440787477280, 360582440905090826, 360582441514861321]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553495649003529, 360553506289303782⟩, ⟨1200637101816455792, 1200935531961557096⟩, true⟩

def words09 : List Nat := [360582442703741807, 360582443892677624, 360582444791127310, 360582445111751241, 360582445177381793, 360582445243173099, 360582445505995595, 360582445506559546, 360582445191631770, 360582444494893218]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk414B

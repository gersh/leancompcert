import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk607A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk607B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk607A

def state06 : KState := ⟨⟨360581931064773147, 360581954591889215⟩, ⟨24787450431087521, 25753171187560433⟩, true⟩

def words05 : List Nat := [360582377160592362, 360582377680425810, 360582377943500074, 360582378056282675, 360582378056995174, 360582378042349577, 360582378282738295, 360582378447946834, 360582378448712020, 360582378442632921]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625268563962632, 360625292099106829⟩, ⟨(-2608558292926571413), (-2607592084341431615)⟩, true⟩

def words06 : List Nat := [360582378700208664, 360582379173412494, 360582379917174520, 360582380661080920, 360582381175783633, 360582381564958287, 360582381946062087, 360582382327399850, 360582382898220177, 360582383605181414]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360620843596580388, 360620867139825309⟩, ⟨(-2339623809713329986), (-2338657108806923560)⟩, true⟩

def words07 : List Nat := [360582384154569167, 360582384704031707, 360582385524058623, 360582386556058064, 360582387326365812, 360582388096776403, 360582388729740671, 360582389092973492, 360582389726732251, 360582390360752788]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605327651117568, 360605351202388667⟩, ⟨(-1396592015728375019), (-1395624826950712997)⟩, true⟩

def words08 : List Nat := [360582390903926872, 360582391177454555, 360582391314830149, 360582391452295124, 360582391520409890, 360582391796166496, 360582392277962476, 360582392759924644, 360582393069792639, 360582393448330489]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360618234922921087, 360618258482221682⟩, ⟨(-2181346884046691904), (-2180379207116138462)⟩, true⟩

def words09 : List Nat := [360582393841049008, 360582394234005961, 360582394897282051, 360582395354127163, 360582395558961003, 360582395763833558, 360582396009628651, 360582396390695331, 360582396981220524, 360582397571922244]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk607B

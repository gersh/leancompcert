import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk991A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk991B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk991A

def state06 : KState := ⟨⟨360584040976833789, 360584106096710862⟩, ⟨(-170488226978218634), (-166128095700636544)⟩, true⟩

def words05 : List Nat := [360582429965890902, 360582430164910301, 360582430299901583, 360582430419477769, 360582430469693823, 360582430520270108, 360582430653836612, 360582430723108321, 360582430741287756, 360582430759676135]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589376055207704, 360589441188712609⟩, ⟨(-699530183442476545), (-695168700762795223)⟩, true⟩

def words06 : List Nat := [360582430765117986, 360582430849720817, 360582431004509866, 360582431159578803, 360582431212772201, 360582431214213657, 360582431236821340, 360582431289803436, 360582431318300126, 360582431390477613]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590442014338695, 360590507161589815⟩, ⟨(-805233663009278004), (-800870817051968024)⟩, true⟩

def words07 : List Nat := [360582431411344138, 360582431432354443, 360582431554708846, 360582431728204397, 360582431875629532, 360582432023323299, 360582432106425701, 360582432154805867, 360582432237389436, 360582432320470529]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588808328843729, 360588873489683450⟩, ⟨(-643216920007975100), (-638852726266498372)⟩, true⟩

def words08 : List Nat := [360582432504658057, 360582432613601900, 360582432644102260, 360582432674737084, 360582432675943578, 360582432722025879, 360582432764560007, 360582432807361705, 360582432808658205, 360582432857708105]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592035365492384, 360592100539937279⟩, ⟨(-963292316780422127), (-958926773474869695)⟩, true⟩

def words09 : List Nat := [360582433025398783, 360582433193509716, 360582433447099812, 360582433599641228, 360582433654558545, 360582433709583454, 360582433734445153, 360582433839286115, 360582433937902420, 360582434036842806]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk991B

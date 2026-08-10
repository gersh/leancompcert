import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk375A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk375B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk375A

def state06 : KState := ⟨⟨360545785198081518, 360545793843424699⟩, ⟨1341411393750554061, 1341630892690418367⟩, true⟩

def words05 : List Nat := [360581516630622372, 360581516448394495, 360581516266080697, 360581516630208301, 360581516630639879, 360581516439075122, 360581516247471785, 360581515603105153, 360581514466205309, 360581513515754050]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580276005979806, 360580284656098168⟩, ⟨45754909673589643, 45974587993281263⟩, true⟩

def words06 : List Nat := [360581512565185795, 360581512323026845, 360581512104313540, 360581511462783234, 360581510821207361, 360581509725157072, 360581508987840106, 360581508958779500, 360581508929672937, 360581508360862429]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360641880443947886, 360641889098842112⟩, ⟨(-2269081344563986216), (-2268861486791302920)⟩, true⟩

def words07 : List Nat := [360581509004164661, 360581509680150090, 360581511063945055, 360581511741943177, 360581511807641119, 360581511873382544, 360581512417142917, 360581513316573195, 360581514923576253, 360581516530608396]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360611642690710045, 360611651350437162⟩, ⟨(-1132816958633763536), (-1132596919217888486)⟩, true⟩

def words08 : List Nat := [360581517781028968, 360581519159288453, 360581520158054204, 360581521156912071, 360581521973762722, 360581522085197189, 360581522085652779, 360581521514153783, 360581521077989711, 360581521880106022]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360558606338877589, 360558615003373134⟩, ⟨861228528046598172, 861448746731664448⟩, true⟩

def words09 : List Nat := [360581523389310697, 360581524898532379, 360581526054777462, 360581526505822748, 360581526650575551, 360581526795457263, 360581526795874379, 360581526692363984, 360581526483119374, 360581525874296849]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk375B

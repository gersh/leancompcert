import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk662A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk662B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk662A

def state06 : KState := ⟨⟨362493673624744744, 362493738502328517⟩, ⟨(-547710526144842827), (-544807100757687539)⟩, true⟩

def words05 : List Nat := [371285516311315017, 371285516410564081, 371285516585540212, 371285516587799340, 371285516483656650, 371285516324754823, 371285516192263924, 371285516194779170, 371285516237500665, 371285516364106069]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 66250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 66200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478243083733278, 362478307981718720⟩, ⟨474776179948106763, 477680957254835829⟩, true⟩

def words06 : List Nat := [371285516488971493, 371285516491270210, 371285516469292902, 371285516514985300, 371285516602787590, 371285516605053227, 371285516459833037, 371285516303165397, 371285516145630573, 371285516084287829]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 66260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 66200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476089816633307, 362476154734993696⟩, ⟨617552269119642729, 620458396777045613⟩, true⟩

def words07 : List Nat := [371285516095708012, 371285516216848240, 371285516337385829, 371285516339656258, 371285516242592416, 371285516155216764, 371285516181927995, 371285516184189478, 371285516044415497, 371285515905735656]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 66270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 66200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489014701099967, 362489079639714298⟩, ⟨(-239171380147080714), (-236263909953807230)⟩, true⟩

def words08 : List Nat := [371285515828786877, 371285515831277029, 371285515781719396, 371285515766834908, 371285515751285566, 371285515700868441, 371285515496896982, 371285515444690983, 371285515541543454, 371285515597688174]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 66280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 66200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489376776583800, 362489441735757776⟩, ⟨(-263133791317002222), (-260224958123818256)⟩, true⟩

def words09 : List Nat := [371285515647201716, 371285515697452726, 371285515974055812, 371285516165485923, 371285516425843662, 371285516687079281, 371285516850076875, 371285516852337305, 371285516771298758, 371285516833295916]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 66290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 66200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 66200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk662B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk752A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk752B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk752A

def state06 : KState := ⟨⟨360569172231320547, 360569208947177180⟩, ⟨980145321866609255, 982011670629465777⟩, true⟩

def words05 : List Nat := [360582258229106955, 360582258158679449, 360582258192712523, 360582258193784063, 360582258160827381, 360582257972923615, 360582257784837542, 360582257523091339, 360582257374436466, 360582257202168271]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360572318151686887, 360572354877746642⟩, ⟨743273146174842968, 745140262876469794⟩, true⟩

def words06 : List Nat := [360582257029749891, 360582256769126843, 360582256490098241, 360582256343451317, 360582256196503614, 360582256005062205, 360582255637097155, 360582255180241709, 360582254723192488, 360582254442817407]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360558694606046315, 360558731342214708⟩, ⟨1768748076113249805, 1770615953741507939⟩, true⟩

def words07 : List Nat := [360582254312180204, 360582254177620676, 360582254042954408, 360582253774131289, 360582253384160238, 360582252949793379, 360582252515107774, 360582252256926567, 360582252056759343, 360582251745425940]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580006764942384, 360580043511222788⟩, ⟨164253539889599519, 166122178801045563⟩, true⟩

def words08 : List Nat := [360582251433858027, 360582251258064273, 360582251170677625, 360582251135834543, 360582251100927453, 360582250896158908, 360582250514867935, 360582250265323779, 360582250015471743, 360582249942074177]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545246391342183, 360545283147849490⟩, ⟨2781585298556102983, 2783454707501354025⟩, true⟩

def words09 : List Nat := [360582249913724146, 360582249797226050, 360582249680509952, 360582249553716775, 360582249533890869, 360582249374730348, 360582249215454298, 360582248949695583, 360582248507486390, 360582248017803028]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk752B

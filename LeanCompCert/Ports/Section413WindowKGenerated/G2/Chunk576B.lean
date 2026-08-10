import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk576A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk576B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk576A

def state06 : KState := ⟨⟨360568963271897616, 360568984371351444⟩, ⟨745040474082363599, 745862418007603713⟩, true⟩

def words05 : List Nat := [360581919825641936, 360581919688513300, 360581919714059311, 360581920030813589, 360581920182725000, 360581920334759261, 360581920335475869, 360581920335860044, 360581920120585317, 360581919897158028]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581736225720561, 360581757332751184⟩, ⟨8437330398161241, 9259711239009597⟩, true⟩

def words06 : List Nat := [360581919673471848, 360581919559327720, 360581919401692965, 360581919052437584, 360581918703062141, 360581918208708601, 360581917987862235, 360581918028245661, 360581918028962633, 360581917896497309]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591880903175960, 360591902017806423⟩, ⟨(-576765893493787786), (-575943074332570592)⟩, true⟩

def words07 : List Nat := [360581918110657138, 360581918327838815, 360581918374914916, 360581918375719556, 360581918122887201, 360581917613520119, 360581917104016616, 360581916827142079, 360581916873506717, 360581917047463805]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566932347922028, 360566953470223413⟩, ⟨862224108885947632, 863047370541824510⟩, true⟩

def words08 : List Nat := [360581917048193335, 360581916980314305, 360581916691217029, 360581916575694378, 360581916459953465, 360581916229220244, 360581915698577177, 360581914884358053, 360581914070013013, 360581913556382918]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567460187516974, 360567481317395994⟩, ⟨831819028859042097, 832642727707371149⟩, true⟩

def words09 : List Nat := [360581913297720079, 360581913218569154, 360581913139333180, 360581912908781315, 360581912805737292, 360581912508488040, 360581912213225606, 360581912214032774, 360581912116535969, 360581911867269606]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk576B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk603A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk603B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk603A

def state06 : KState := ⟨⟨360607882247541515, 360607905453802385⟩, ⟨(-1544853603772942820), (-1543907314071875160)⟩, true⟩

def words05 : List Nat := [360582322410950552, 360582322776067265, 360582323415628491, 360582324263217991, 360582325040142908, 360582325817180176, 360582326365579159, 360582326709727225, 360582327134183099, 360582327558902171]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579430999440978, 360579454213662936⟩, ⟨172539234517046218, 173486004790281610⟩, true⟩

def words06 : List Nat := [360582327975105203, 360582328117911135, 360582328118672231, 360582328089731550, 360582328060653883, 360582327998351260, 360582328019798724, 360582328041426054, 360582328042178600, 360582327925850948]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601212228395985, 360601235450591112⟩, ⟨(-1142504353057037553), (-1141557101405766027)⟩, true⟩

def words07 : List Nat := [360582328032680777, 360582328187368588, 360582328616191314, 360582328771747752, 360582328772542320, 360582328657370216, 360582328643794890, 360582328923557919, 360582329237371231, 360582329551361127]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602085752029129, 360602108982291059⟩, ⟨(-1195286588881528346), (-1194338850118130084)⟩, true⟩

def words08 : List Nat := [360582329728015420, 360582330011439052, 360582330568986291, 360582331126766098, 360582331533287790, 360582331726715552, 360582331782164837, 360582331837705406, 360582331884936140, 360582332213399699]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593528899795849, 360593552138009830⟩, ⟨(-678491387129500391), (-677543168101867025)⟩, true⟩

def words09 : List Nat := [360582332757611653, 360582333301967624, 360582333677389778, 360582333779630248, 360582333780337701, 360582333770050858, 360582334022457336, 360582334348527420, 360582334535012963, 360582334721607753]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk603B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk887A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk887B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk887A

def state06 : KState := ⟨⟨360574139569180838, 360574191299166005⟩, ⟨698104987097832872, 701205624986581670⟩, true⟩

def words05 : List Nat := [360582091850111062, 360582091950812981, 360582092019038686, 360582092020317983, 360582091989222835, 360582091836654906, 360582091683849595, 360582091512608459, 360582091405131363, 360582091317473651]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555690928922199, 360555742671087244⟩, ⟨2335602717373317422, 2338704436407855208⟩, true⟩

def words06 : List Nat := [360582091229610312, 360582091078344106, 360582090800062761, 360582090596781989, 360582090393160179, 360582090128815346, 360582089737599530, 360582089246425881, 360582088755016108, 360582088333320069]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545928866358289, 360545980620566483⟩, ⟨3202318639188538106, 3205421427353963374⟩, true⟩

def words07 : List Nat := [360582088037572088, 360582087868737159, 360582087699766587, 360582087459165222, 360582087274320619, 360582087030130752, 360582086785560709, 360582086579157506, 360582086245878403, 360582085840518657]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557747967775259, 360557799734078747⟩, ⟨2152890883427154764, 2155994745472108510⟩, true⟩

def words08 : List Nat := [360582085434901012, 360582084964136015, 360582084556675461, 360582084236749231, 360582083916740862, 360582083487380997, 360582082963835947, 360582082496724765, 360582082029223141, 360582081688639758]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556790605867347, 360556842384351272⟩, ⟨2237880113190218313, 2240985056797193197⟩, true⟩

def words09 : List Nat := [360582081416310036, 360582081056525555, 360582080696495174, 360582080463466623, 360582080294171314, 360582080015668991, 360582079737033245, 360582079395048068, 360582078985291542, 360582078702558448]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk887B

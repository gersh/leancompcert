import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk475A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk475B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk475A

def state06 : KState := ⟨⟨360540826499978580, 360540840632132096⟩, ⟨1991853321670448266, 1992307504196527048⟩, true⟩

def words05 : List Nat := [360582738215613562, 360582737628986092, 360582737042315859, 360582736112189867, 360582735255402683, 360582734288544602, 360582733321530112, 360582732547944431, 360582731913949555, 360582731033818314]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599537036942367, 360599551175267742⟩, ⟨(-800710574366408669), (-800256098276634677)⟩, true⟩

def words06 : List Nat := [360582730153575190, 360582729632571552, 360582729474270873, 360582729615805229, 360582729616424482, 360582729331457493, 360582728907546763, 360582728614880131, 360582728469140016, 360582728823450950]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567217375647721, 360567231520211653⟩, ⟨736976494408228488, 737431267296542190⟩, true⟩

def words07 : List Nat := [360582728903787916, 360582728984204240, 360582729414190113, 360582730068854096, 360582730424344806, 360582730779924342, 360582730915553599, 360582730916207930, 360582730610811097, 360582730285812674]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574314651606874, 360574328802330599⟩, ⟨399258754049514025, 399713820051629625⟩, true⟩

def words08 : List Nat := [360582730075133098, 360582730075787788, 360582729945108545, 360582729503556705, 360582729061917206, 360582728427509340, 360582728217058166, 360582728211130076, 360582728205131306, 360582727916011029]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589708618745412, 360589722775657005⟩, ⟨(-333487266527267170), (-333031906013820138)⟩, true⟩

def words09 : List Nat := [360582728003667463, 360582728267996608, 360582728344554096, 360582728345208845, 360582728129941101, 360582727547760923, 360582726965483387, 360582726451806942, 360582726306351318, 360582726454024817]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk475B

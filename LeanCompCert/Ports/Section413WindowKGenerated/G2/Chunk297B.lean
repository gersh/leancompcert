import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk297A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk297B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk297A

def state06 : KState := ⟨⟨360580923161512600, 360580928484649806⟩, ⟨76756431552736641, 76863567788246535⟩, true⟩

def words05 : List Nat := [360583509376108543, 360583509042988490, 360583509501756919, 360583511058147741, 360583511854582918, 360583512651026768, 360583512651386043, 360583512563762790, 360583511352165616, 360583511265825487]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611628993677290, 360611634320529677⟩, ⟨(-837222267372579273), (-837115020554570407)⟩, true⟩

def words06 : List Nat := [360583512217552186, 360583512750405129, 360583512750760012, 360583512704303155, 360583512657778519, 360583512952167574, 360583513789473436, 360583514626797526, 360583514903910109, 360583515848843991]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360617289308583897, 360617294639164730⟩, ⟨(-1005945536275306271), (-1005838178442644287)⟩, true⟩

def words07 : List Nat := [360583516768303456, 360583517687814922, 360583519092941385, 360583519375227796, 360583519375592129, 360583518699037341, 360583518022454836, 360583517877013011, 360583519011542029, 360583520146083818]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360555209577467539, 360555214911810464⟩, ⟨842696769972774938, 842804239858830734⟩, true⟩

def words08 : List Nat := [360583520720590418, 360583520720985143, 360583520172951220, 360583519449689276, 360583518726376889, 360583516961866562, 360583514466495854, 360583511412329548, 360583508358290399, 360583506427079307]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360478478745365950, 360478484083433837⟩, ⟨3129056120995215635, 3129163701866174591⟩, true⟩

def words09 : List Nat := [360583505477732601, 360583505227526577, 360583504977286745, 360583504168493232, 360583502238122693, 360583499718131424, 360583497198192041, 360583495507695176, 360583493100168420, 360583489576785051]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk297B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk704A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk704B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk704A

def state06 : KState := ⟨⟨360591589449632653, 360591621463716813⟩, ⟨(-646470804641462198), (-644947159711193422)⟩, true⟩

def words05 : List Nat := [360582469244024255, 360582469149764600, 360582469097273985, 360582469098272091, 360582468940097400, 360582468567409569, 360582468194541273, 360582468022958540, 360582468082608849, 360582468213554153]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587735357031994, 360587767380642758⟩, ⟨(-374945953178234281), (-373421636957643691)⟩, true⟩

def words06 : List Nat := [360582468243340449, 360582468282256688, 360582468442530895, 360582468603092841, 360582468643233958, 360582468654416596, 360582468655306427, 360582468559972119, 360582468464463430, 360582468440128822]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360547880338790278, 360547912371802911⟩, ⟨2433905486803995768, 2435430465620818732⟩, true⟩

def words07 : List Nat := [360582468604904285, 360582468769865883, 360582468804891029, 360582468805889560, 360582468687059818, 360582468517591228, 360582468347821259, 360582468137241306, 360582467776856530, 360582467287603434]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593617628621207, 360593649671077992⟩, ⟨(-789940480476264656), (-788414835990288666)⟩, true⟩

def words08 : List Nat := [360582466798138103, 360582466509837102, 360582466360108777, 360582466206245858, 360582466052310265, 360582465707344970, 360582465303395745, 360582465100586401, 360582464897472020, 360582465054091565]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566219499370570, 360566251551336543⟩, ⟨1141588566032055456, 1143114880866780984⟩, true⟩

def words09 : List Nat := [360582465113074638, 360582465172164819, 360582465391960956, 360582465726988668, 360582465953092996, 360582466179352576, 360582466247942336, 360582466248941300, 360582466175663385, 360582465946809831]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk704B

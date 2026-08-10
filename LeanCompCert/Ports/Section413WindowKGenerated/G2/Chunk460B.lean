import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk460A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk460B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk460A

def state06 : KState := ⟨⟨360536696121982715, 360536709341767932⟩, ⟨2142551135873338208, 2142962606505098452⟩, true⟩

def words05 : List Nat := [360583235577946187, 360583236531056887, 360583237042474225, 360583237083497157, 360583237084025814, 360583236921522370, 360583236758843066, 360583236519375951, 360583235809469267, 360583234800007296]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 46050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 46000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575355504067988, 360575368729812326⟩, ⟨361766196888844222, 362177942027225438⟩, true⟩

def words06 : List Nat := [360583233790434516, 360583233251324511, 360583233004673512, 360583233054514728, 360583233055097555, 360583232668003596, 360583232005273937, 360583231331556790, 360583230657679921, 360583230200227504]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 46060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 46000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552753904022869, 360552767135788322⟩, ⟨1403257360809287772, 1403669383371288014⟩, true⟩

def words07 : List Nat := [360583230030157460, 360583229623289116, 360583229278779083, 360583229700392489, 360583229853204775, 360583230006111737, 360583230006674650, 360583229924059024, 360583229371294001, 360583228710948290]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 46070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 46000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360521695104862160, 360521708342586288⟩, ⟨2834430505358076520, 2834842802526250344⟩, true⟩

def words08 : List Nat := [360583228050424485, 360583227217255885, 360583225914059531, 360583224375569152, 360583222837044749, 360583221038906146, 360583219477242207, 360583218074395040, 360583216671534621, 360583215020879329]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 46080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 46000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583388570264129, 360583401813951430⟩, ⟨(-9362065961099651), (-8949493920872469)⟩, true⟩

def words09 : List Nat := [360583213686928692, 360583212822809224, 360583211958541094, 360583211563999603, 360583210972066893, 360583209935260698, 360583208898378545, 360583208141627586, 360583207681107066, 360583207685973277]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 46090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 46000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 46000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk460B

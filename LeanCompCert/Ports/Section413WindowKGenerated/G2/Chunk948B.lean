import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk948A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk948B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk948A

def state06 : KState := ⟨⟨360591422222419039, 360591481613269066⟩, ⟨(-890899745962525123), (-887095484918288195)⟩, true⟩

def words05 : List Nat := [360582128742115912, 360582128911745575, 360582129097812975, 360582129339491895, 360582129535799423, 360582129732327252, 360582129843316581, 360582129883427084, 360582129983123644, 360582130083294490]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585289980247677, 360585349384036632⟩, ⟨(-309211009801454822), (-305405521305743660)⟩, true⟩

def words06 : List Nat := [360582130215903969, 360582130238019296, 360582130239243903, 360582130198218204, 360582130156935040, 360582130089723400, 360582130141588620, 360582130193714739, 360582130194951008, 360582130217786611]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360605797068224038, 360605856485013696⟩, ⟨(-2254864889231243026), (-2251058167297363136)⟩, true⟩

def words07 : List Nat := [360582130250145332, 360582130282888426, 360582130426303320, 360582130583510859, 360582130625216718, 360582130667016814, 360582130746314826, 360582130914468163, 360582131165638198, 360582131417114988]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360607374054338806, 360607433484211055⟩, ⟨(-2404610806756968045), (-2400802843480398579)⟩, true⟩

def words08 : List Nat := [360582131612586924, 360582131697485867, 360582131873452574, 360582132049819535, 360582132150057749, 360582132283121710, 360582132344396137, 360582132405803366, 360582132577979300, 360582132846179204]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590225311480901, 360590284754323770⟩, ⟨(-777228139308483189), (-773418945184814637)⟩, true⟩

def words09 : List Nat := [360582133181424597, 360582133516949823, 360582133789842427, 360582134025028171, 360582134231796214, 360582134438938953, 360582134662385588, 360582134834942216, 360582134922067547, 360582135009377091]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk948B

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk085

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360273298122960953, 360273298509543851⟩, ⟨2597732237952150349, 2597734465856441707⟩, true⟩

def state01 : KState := ⟨⟨360470795895527195, 360470796283064205⟩, ⟨918024443145343382, 918026679164275070⟩, true⟩

def words00 : List Nat := [360578878378565527, 360578856126356605, 360578842355247356, 360578830460186364, 360578818567917060, 360578793604454904, 360578754924612717, 360578724710163538, 360578694502787000, 360578672508582922]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360347658077466217, 360347658465968615⟩, ⟨1967178656079772029, 1967180900318955019⟩, true⟩

def words01 : List Nat := [360578659833755268, 360578640318498891, 360578620807806301, 360578620511522876, 360578620511608124, 360578617671998529, 360578614833044958, 360578601935475176, 360578575345806376, 360578548243001357]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360392858255231816, 360392858644688574⟩, ⟨1581579553949595387, 1581581806324771327⟩, true⟩

def words02 : List Nat := [360578521146524799, 360578507678737863, 360578480525382053, 360578446298479446, 360578412079590922, 360578368106725540, 360578335745814230, 360578316998887397, 360578298256345091, 360578272689978700]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360549952999472264, 360549953389888279⟩, ⟨239955083058074779, 239957343620495365⟩, true⟩

def words03 : List Nat := [360578250955909732, 360578234801273217, 360578218650394302, 360578196552664808, 360578170901886372, 360578133266183991, 360578095639278852, 360578071598145436, 360578054729940845, 360578051439492553]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360382384795434228, 360382385186818222⟩, ⟨1670977684293335387, 1670979953127003345⟩, true⟩

def words04 : List Nat := [360578048149799741, 360578036027602785, 360578010293297223, 360577998129327204, 360577985968177754, 360577970365182666, 360577941157235873, 360577898374210268, 360577855601174369, 360577821438645942]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360346021965528599, 360346022357871454⟩, ⟨1982289249867410193, 1982291526904124513⟩, true⟩

def words05 : List Nat := [360577798583360648, 360577779996676689, 360577761414327936, 360577736061756052, 360577717471273565, 360577690830308212, 360577664195540066, 360577645617186666, 360577625527167243, 360577598470827544]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360313546652930340, 360313547046236818⟩, ⟨2260933861232350855, 2260936146522566771⟩, true⟩

def words06 : List Nat := [360577571420787375, 360577543878311200, 360577523459344592, 360577516532951980, 360577509608168763, 360577490805732225, 360577458461690357, 360577429952395187, 360577401449722334, 360577366899973407]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360225434888010055, 360225435282287726⟩, ⟨3016823903260603237, 3016826196878789461⟩, true⟩

def words07 : List Nat := [360577336119542391, 360577298602058329, 360577261093307477, 360577237052209420, 360577220095675535, 360577193878950779, 360577167668328977, 360577134438590241, 360577087712159848, 360577046727145394]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360281093798809646, 360281094194050270⟩, ⟨2539369105676333078, 2539371407561526092⟩, true⟩

def words08 : List Nat := [360577005751649030, 360576978219656604, 360576951488189409, 360576918037455986, 360576884594499022, 360576841941628612, 360576806890329603, 360576779347384737, 360576751810843635, 360576713682707026]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360387832121884789, 360387832518090343⟩, ⟨1621023564189791992, 1621025874368653832⟩, true⟩

def words09 : List Nat := [360576679272420516, 360576644622211321, 360576609980037835, 360576579188385145, 360576534954152510, 360576479204496611, 360576423467789272, 360576381127402344, 360576345818876217, 360576323898830885]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk085

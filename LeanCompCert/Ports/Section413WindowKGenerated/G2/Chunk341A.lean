import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk341A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562651995738645, 360562659065262894⟩, ⟨644632966174414198, 644795956328181456⟩, true⟩

def state01 : KState := ⟨⟨360544700948295854, 360544708022168277⟩, ⟨1256701824519996169, 1256864962967684037⟩, true⟩

def words00 : List Nat := [360581567483501028, 360581566482181536, 360581565384566077, 360581564883251084, 360581564381836520, 360581563457526003, 360581561676522165, 360581559463150927, 360581557249822725, 360581555426535551]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360490922515443662, 360490929593621459⟩, ⟨3091282424278179666, 3091445709604210974⟩, true⟩

def words01 : List Nat := [360581554346693229, 360581552820212992, 360581551293770162, 360581549280356235, 360581546794827993, 360581544091137192, 360581541387471415, 360581539351966596, 360581537339847171, 360581534684758746]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583030463054501, 360583037545543740⟩, ⟨(-51880617097949073), (-51717184644640399)⟩, true⟩

def words02 : List Nat := [360581532029722784, 360581529998847352, 360581528649796243, 360581528158424145, 360581527667053910, 360581526390550876, 360581524496793289, 360581523460646349, 360581522424421470, 360581522290067937]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360547020755990711, 360547027842836207⟩, ⟨1177289155144212006, 1177452736298470186⟩, true⟩

def words03 : List Nat := [360581522290475273, 360581521844487010, 360581521398431764, 360581520747123686, 360581520527265702, 360581520089464634, 360581519651641879, 360581518784787282, 360581517802076957, 360581516792347000]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577983682764070, 360577990773911898⟩, ⟨120028043508028403, 120191771565715923⟩, true⟩

def words04 : List Nat := [360581515782525156, 360581515629603244, 360581514966115490, 360581513766622551, 360581512567122353, 360581511150138653, 360581510511557904, 360581510620803447, 360581510621210707, 360581510298701524]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk341A

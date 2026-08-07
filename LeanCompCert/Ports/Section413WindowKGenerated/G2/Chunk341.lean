import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk341

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

def state06 : KState := ⟨⟨360568657053243481, 360568664148712204⟩, ⟨438274953693474421, 438438829330738715⟩, true⟩

def words05 : List Nat := [360581510196015571, 360581509956113442, 360581509716099379, 360581508941963448, 360581507313994284, 360581504795763743, 360581502277593306, 360581500615756142, 360581499384313024, 360581499009055610]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590996368213750, 360591003468037390⟩, ⟨(-325140790528978767), (-324976766106965383)⟩, true⟩

def words06 : List Nat := [360581498633746292, 360581497735039656, 360581496944548899, 360581496787527437, 360581496630387360, 360581496256031065, 360581495758362941, 360581494610242021, 360581493462101034, 360581493159117342]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560514577640495, 360560521681768929⟩, ⟨716781335131715244, 716945506670993468⟩, true⟩

def words07 : List Nat := [360581494293174880, 360581495427253527, 360581496133423729, 360581496861805499, 360581497361101726, 360581497860489232, 360581498061848092, 360581498062306280, 360581497880326164, 360581497267101609]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588103859872953, 360588110968329234⟩, ⟨(-226459338775321169), (-226295019289798241)⟩, true⟩

def words08 : List Nat := [360581496653816768, 360581495730727368, 360581495638606030, 360581496020247695, 360581496020669828, 360581495644210229, 360581494415652630, 360581493465821249, 360581492515899382, 360581492413174668]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360545436383341948, 360545443496157673⟩, ⟨1232632212236588278, 1232796680792737964⟩, true⟩

def words09 : List Nat := [360581492413586604, 360581492051792318, 360581491839074652, 360581492532339007, 360581492636342223, 360581492740407509, 360581492740815406, 360581492414398360, 360581491236229804, 360581490182730561]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk341

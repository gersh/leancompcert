import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk445

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362463277228570748, 362463305572749640⟩, ⟨988735059264697713, 989587277713818903⟩, true⟩

def state01 : KState := ⟨⟨362506747784579628, 362506776141916314⟩, ⟨(-945864460700269616), (-945011656660257582)⟩, true⟩

def words00 : List Nat := [371285542995217709, 371285542996838941, 371285542958354560, 371285543167628945, 371285543263194777, 371285543264706261, 371285543516283674, 371285543895504789, 371285544694500617, 371285545173017385]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494526054055895, 362494554424841941⟩, ⟨(-401807206840480545), (-400953804103738163)⟩, true⟩

def words01 : List Nat := [371285545598703924, 371285546024895307, 371285546661611596, 371285547048282875, 371285547523087641, 371285547998420901, 371285548369911252, 371285548371383499, 371285548272837201, 371285548476994774]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475434182992872, 362475462566885542⟩, ⟨448302787531852140, 449156773843095212⟩, true⟩

def words02 : List Nat := [371285549158584116, 371285549240666216, 371285549241781542, 371285549217648332, 371285549239412916, 371285549241035623, 371285549101995279, 371285549139181574, 371285549176046743, 371285549177571442]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362523663188056362, 362523691585242944⟩, ⟨(-1699526176606323873), (-1698671598248909791)⟩, true⟩

def words03 : List Nat := [371285549229401790, 371285549508489245, 371285550290615595, 371285550653886243, 371285550939282720, 371285551225140668, 371285552014144081, 371285552612290453, 371285553469582762, 371285554327474845]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362504072297722998, 362504100708234057⟩, ⟨(-826961598235838422), (-826106426342902208)⟩, true⟩

def words04 : List Nat := [371285555065156452, 371285555131631923, 371285555701244526, 371285556271616812, 371285556916377378, 371285556917850582, 371285556891227894, 371285556877852868, 371285557352396890, 371285557770334955]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362466898591682808, 362466927015452245⟩, ⟨829378778547089843, 830234541169669779⟩, true⟩

def words05 : List Nat := [371285558379870686, 371285558989984331, 371285559599681362, 371285559601154818, 371285559539569925, 371285559482071959, 371285559679322343, 371285559680796039, 371285559266323119, 371285558849859105]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471696224878190, 362471724661850646⟩, ⟨615667922110884311, 616524273128846103⟩, true⟩

def words06 : List Nat := [371285558432746234, 371285558276098219, 371285558100096503, 371285558264755008, 371285558351875342, 371285558353349346, 371285557769492609, 371285557569847887, 371285557379039924, 371285557380565676]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483426206967345, 362483454657364000⟩, ⟨92812612397637205, 93669561799461541⟩, true⟩

def words07 : List Nat := [371285557071315532, 371285556759247660, 371285556455776951, 371285556457411207, 371285556363447039, 371285556394546399, 371285556406787330, 371285556408263017, 371285555859301581, 371285555813976819]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473848786201561, 362473877249743964⟩, ⟨519804202059252123, 520661737566871009⟩, true⟩

def words08 : List Nat := [371285556174854256, 371285556176328979, 371285555914112568, 371285555497960035, 371285555081249934, 371285554749051424, 371285554166078422, 371285554086331409, 371285554006103877, 371285553897816781]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489711270225697, 362489739747101335⟩, ⟨(-187590616478356289), (-186732486373736119)⟩, true⟩

def words09 : List Nat := [371285553636959951, 371285553582844449, 371285553840555880, 371285553842040870, 371285553705344080, 371285553485449239, 371285553264997265, 371285553170431452, 371285552918380865, 371285553013925538]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk445

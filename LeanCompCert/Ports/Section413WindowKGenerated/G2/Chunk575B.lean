import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk575A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk575B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk575A

def state06 : KState := ⟨⟨360606272124748245, 360606293148086103⟩, ⟨(-1402457458315733278), (-1401639899427272898)⟩, true⟩

def words05 : List Nat := [360581943230497585, 360581942919810131, 360581942608892215, 360581942509795876, 360581942418208415, 360581942066839364, 360581941715328825, 360581941787141365, 360581942210850921, 360581942634727627]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582496807976820, 360582517838975676⟩, ⟨(-33972047173465885), (-33154047281850017)⟩, true⟩

def words06 : List Nat := [360581942828436717, 360581942921802417, 360581943060170237, 360581943198777988, 360581943199450536, 360581943199949288, 360581942977232652, 360581942587387673, 360581942197389496, 360581941957936927]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545739150042444, 360545760188599150⟩, ⟨2082501124915413129, 2083319559950641807⟩, true⟩

def words07 : List Nat := [360581942270280432, 360581942582767345, 360581942745278265, 360581942864474542, 360581942865159475, 360581942764630619, 360581942663873091, 360581942543146591, 360581942121458068, 360581941493912639]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570571944442697, 360570592990591973⟩, ⟨652577965598796967, 653396837851385361⟩, true⟩

def words08 : List Nat := [360581940866207181, 360581940451599684, 360581940311333228, 360581940355689318, 360581940356435002, 360581940096787348, 360581939536177028, 360581939277346287, 360581939018301663, 360581938655427038]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579157010302277, 360579178064108104⟩, ⟨158123068228297037, 158942381458643889⟩, true⟩

def words09 : List Nat := [360581938459146129, 360581938098519625, 360581937737750666, 360581937811233153, 360581937867615444, 360581937924148576, 360581937924864489, 360581937814185718, 360581937527434386, 360581937480452873]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk575B

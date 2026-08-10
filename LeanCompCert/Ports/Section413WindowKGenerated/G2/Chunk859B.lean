import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk859A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk859B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk859A

def state06 : KState := ⟨⟨360558206934810374, 360558255332527815⟩, ⟨2065642626580791112, 2068452130827426700⟩, true⟩

def words05 : List Nat := [360582319426144230, 360582319422242149, 360582319418221069, 360582319310749435, 360582319182865409, 360582319021307252, 360582318859379605, 360582318783550513, 360582318572199493, 360582318293565827]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360555075406283756, 360555123815661501⟩, ⟨2334899157632094012, 2337709664257754764⟩, true⟩

def words06 : List Nat := [360582318014636100, 360582317832514797, 360582317718267409, 360582317621336402, 360582317524319385, 360582317293762803, 360582316971960769, 360582316647060285, 360582316321797793, 360582315971811993]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552735174186803, 360552783595329617⟩, ⟨2536116549850595349, 2538928067976797961⟩, true⟩

def words07 : List Nat := [360582315656618702, 360582315273810785, 360582314890774899, 360582314613958534, 360582314449879030, 360582314220910205, 360582313991814258, 360582313675702146, 360582313224038005, 360582312882000667]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360542473073349450, 360542521506149718⟩, ⟨3418466651979171458, 3421279172471993052⟩, true⟩

def words08 : List Nat := [360582312539577850, 360582312166390828, 360582311754620626, 360582311275275978, 360582310795741697, 360582310252203307, 360582309802320599, 360582309373648126, 360582308944828402, 360582308448497340]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578645364090393, 360578693808561100⟩, ⟨307811023071020933, 310624547159546739⟩, true⟩

def words09 : List Nat := [360582307986809431, 360582307660555974, 360582307333946982, 360582307118880276, 360582306900562134, 360582306558661462, 360582306216533188, 360582305938654077, 360582305762617545, 360582305721900165]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk859B

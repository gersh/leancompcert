import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk676A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk676B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk676A

def state06 : KState := ⟨⟨360539903176555925, 360539932601750596⟩, ⟨2904561753692080327, 2905906583680650947⟩, true⟩

def words05 : List Nat := [360582883683825137, 360582883762917811, 360582883763776875, 360582883732692722, 360582883483245767, 360582883083282778, 360582882683052123, 360582882400280944, 360582881899206798, 360582881265417174]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360562461005262410, 360562490439488366⟩, ⟨1378201325439482967, 1379546766528744649⟩, true⟩

def words06 : List Nat := [360582880631432415, 360582880031557587, 360582879600465324, 360582879325086672, 360582879049646148, 360582878582308386, 360582878016131232, 360582877622563920, 360582877228741708, 360582876825871235]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565282233968417, 360565311677305170⟩, ⟨1187201711072888127, 1188547768734628057⟩, true⟩

def words07 : List Nat := [360582876525473417, 360582876098661718, 360582875671674446, 360582875252950693, 360582874943818912, 360582874578798588, 360582874213670626, 360582873697418109, 360582873220682811, 360582872962304205]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570799190738110, 360570828643083538⟩, ⟨813725361455678197, 815072028869994367⟩, true⟩

def words08 : List Nat := [360582872703605742, 360582872594492312, 360582872350012575, 360582871906071463, 360582871461987680, 360582870963203143, 360582870598803799, 360582870408840160, 360582870218787976, 360582869890370730]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590838536297092, 360590867997664118⟩, ⟨(-542886698382693281), (-541539420251308503)⟩, true⟩

def words09 : List Nat := [360582869713262215, 360582869515542165, 360582869317547625, 360582869347518781, 360582869348400477, 360582869214364242, 360582869080164112, 360582868872295099, 360582868891499716, 360582869010643967]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk676B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk826A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk826B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk826A

def state06 : KState := ⟨⟨360599139574814483, 360599184192307566⟩, ⟨(-1391807928194444774), (-1389317178104242224)⟩, true⟩

def words05 : List Nat := [360582374489460706, 360582374763566058, 360582374964111287, 360582375252365572, 360582375480955740, 360582375709890128, 360582376084765948, 360582376375048986, 360582376579441609, 360582376784000091]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607851850095849, 360607896478786976⟩, ⟨(-2112002780273533336), (-2109511104498096562)⟩, true⟩

def words06 : List Nat := [360582377104792914, 360582377521967472, 360582377926678115, 360582378331589055, 360582378590933223, 360582378704365177, 360582378861333353, 360582379018641321, 360582379226970378, 360582379536878712]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599545330614626, 360599589970591831⟩, ⟨(-1425254793446377469), (-1422762184595910075)⟩, true⟩

def words07 : List Nat := [360582379746415017, 360582379956072709, 360582380266236599, 360582380651047377, 360582380996904784, 360582381342954077, 360582381573645246, 360582381702758028, 360582381911847931, 360582382121332680]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587916964636233, 360587961615767929⟩, ⟨(-463772495000422777), (-461278963838841863)⟩, true⟩

def words08 : List Nat := [360582382440971014, 360582382614899554, 360582382715272406, 360582382815782868, 360582382838371240, 360582382934445821, 360582383052308936, 360582383170395639, 360582383201627050, 360582383270315113]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360600485622591552, 360600530284929237⟩, ⟨(-1503238168353879860), (-1500743710514148512)⟩, true⟩

def words09 : List Nat := [360582383334721344, 360582383399469671, 360582383507650843, 360582383508836347, 360582383503691302, 360582383356817015, 360582383209719559, 360582383222795522, 360582383443186364, 360582383663842260]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk826B

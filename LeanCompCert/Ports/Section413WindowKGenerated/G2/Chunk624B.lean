import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk624A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk624B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk624A

def state06 : KState := ⟨⟨360604229889337321, 360604254805904388⟩, ⟨(-1347418628416522379), (-1346367297703810601)⟩, true⟩

def words05 : List Nat := [360582698433910183, 360582698339141099, 360582698244204576, 360582698437911017, 360582698569600036, 360582698701428341, 360582698702209269, 360582698786675941, 360582699132501830, 360582699478616900]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586268186780991, 360586293111611729⟩, ⟨(-225522768025805308), (-224470921122463746)⟩, true⟩

def words06 : List Nat := [360582699817532370, 360582699901200600, 360582699901981810, 360582699837872666, 360582699773626450, 360582699545307130, 360582699667870759, 360582699857722205, 360582699858515777, 360582699909628050]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360619090012868779, 360619114945977213⟩, ⟨(-2276103807943642051), (-2275051443893108965)⟩, true⟩

def words07 : List Nat := [360582700172296951, 360582700435216744, 360582700953891102, 360582701217408370, 360582701218234269, 360582701215152032, 360582701463940819, 360582701886464566, 360582702469969121, 360582703053659659]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360610169645765748, 360610194587221199⟩, ⟨(-1718746253976619055), (-1717693368362982511)⟩, true⟩

def words08 : List Nat := [360582703478862309, 360582703910833709, 360582704598562814, 360582705286527603, 360582705909156951, 360582706333205058, 360582706603107517, 360582706873089791, 360582707094328610, 360582707535191900]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554948828287387, 360554973778005842⟩, ⟨1732243071341575743, 1733296473351392859⟩, true⟩

def words09 : List Nat := [360582707777358825, 360582708019677702, 360582708093147219, 360582708094024364, 360582707912303332, 360582707611322149, 360582707310066697, 360582707264843581, 360582706964401365, 360582706521579465]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk624B

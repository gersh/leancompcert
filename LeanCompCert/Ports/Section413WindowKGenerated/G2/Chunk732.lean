import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk732

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587876438401103, 360587911095766538⟩, ⟨(-401788529522751039), (-400074992975800901)⟩, true⟩

def state01 : KState := ⟨⟨360587013040487898, 360587047707652394⟩, ⟨(-338580996485014557), (-336866742598100173)⟩, true⟩

def words00 : List Nat := [360582445875127832, 360582446023030107, 360582446052893534, 360582446082865097, 360582446083741806, 360582446045137189, 360582446179618734, 360582446314293957, 360582446330498439, 360582446394426266]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589914327688656, 360589949004686019⟩, ⟨(-551008705919149510), (-549293732118162298)⟩, true⟩

def words01 : List Nat := [360582446610714076, 360582446827301169, 360582447039512580, 360582447065617854, 360582447066586528, 360582446936098180, 360582446823763089, 360582446937269883, 360582447040573032, 360582447144125277]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574722849362857, 360574757536269105⟩, ⟨561319710093076634, 563035409471047388⟩, true⟩

def words02 : List Nat := [360582447154502225, 360582447155543570, 360582447061704907, 360582447068980546, 360582447069853397, 360582446975334204, 360582446893951120, 360582446640615662, 360582446387092345, 360582446125774377]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575628639692868, 360575663336394068⟩, ⟨495012719651278011, 496729136362872025⟩, true⟩

def words03 : List Nat := [360582446050225369, 360582446079867094, 360582446080803349, 360582446000650995, 360582445925753545, 360582445767825629, 360582445636663599, 360582445638030095, 360582445638957608, 360582445547431246]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593152570012385, 360593187276554805⟩, ⟨(-788513782590950311), (-786796645060243837)⟩, true⟩

def words04 : List Nat := [360582445455686297, 360582445383613576, 360582445593935516, 360582445804450970, 360582445860097233, 360582445861138511, 360582445857713059, 360582445926842121, 360582446024348761, 360582446172063942]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360574594372129105, 360574629088594726⟩, ⟨570946459237246010, 572664323689210150⟩, true⟩

def words05 : List Nat := [360582446226405125, 360582446280848669, 360582446328143613, 360582446492261429, 360582446493153874, 360582446480358722, 360582446467450576, 360582446361810051, 360582446069924571, 360582445964429960]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360587185727464029, 360587220453743608⟩, ⟨(-351556594306360489), (-349838010833549403)⟩, true⟩

def words06 : List Nat := [360582445882962767, 360582445913774594, 360582445914702427, 360582445852681826, 360582445790491050, 360582445681458505, 360582445761215652, 360582445857491649, 360582445858444533, 360582445877023848]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607260513787808, 360607295249891337⟩, ⟨(-1822622705602211876), (-1820903402280027962)⟩, true⟩

def words07 : List Nat := [360582445971782803, 360582446066839560, 360582446288869042, 360582446325122556, 360582446326084235, 360582446202968764, 360582446141374570, 360582446336246466, 360582446676183981, 360582447016348127]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586853045417442, 360586887791454723⟩, ⟨(-327192705231245818), (-325472673915162184)⟩, true⟩

def words08 : List Nat := [360582447238810430, 360582447434560881, 360582447532384699, 360582447630494941, 360582447681282668, 360582447682324151, 360582447547269087, 360582447284835780, 360582447022210409, 360582446964151028]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360559819331707705, 360559854087547823⟩, ⟨1654338613976945162, 1656059363792645188⟩, true⟩

def words09 : List Nat := [360582447211410958, 360582447458863682, 360582447563894747, 360582447613942336, 360582447614814304, 360582447592139327, 360582447569163881, 360582447493632995, 360582447291884276, 360582446984734626]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk732

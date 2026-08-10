import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk732A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk732A

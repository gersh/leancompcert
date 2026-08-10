import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk238A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617030334506735, 360617033673410222⟩, ⟨(-834320672852771860), (-834266911202132032)⟩, true⟩

def state01 : KState := ⟨⟨360628004456307237, 360628007798132464⟩, ⟨(-1095372049306568074), (-1095318218103561868)⟩, true⟩

def words00 : List Nat := [360581985149124130, 360581989265906347, 360581993888417751, 360581998510600747, 360582001486148800, 360582002710768661, 360582003289901113, 360582003869070729, 360582005352700532, 360582007285003929]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360624912256998436, 360624915601774092⟩, ⟨(-1021684928740314405), (-1021631027273102235)⟩, true⟩

def words01 : List Nat := [360582008332850255, 360582009380642315, 360582012188015582, 360582016350761186, 360582019343583233, 360582022336204113, 360582024127060803, 360582024168814839, 360582025969713581, 360582027770563266]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611300980465593, 360611304328164793⟩, ⟨(-697631582735459648), (-697577611615079438)⟩, true⟩

def words02 : List Nat := [360582028947936173, 360582029087939726, 360582029088218518, 360582028331769489, 360582027575333858, 360582026545910082, 360582028503409442, 360582030460809485, 360582031243009206, 360582032471691499]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360696315501029068, 360696318851653106⟩, ⟨(-2723902398711951907), (-2723848357878137325)⟩, true⟩

def words03 : List Nat := [360582035458057358, 360582038444266131, 360582043187840006, 360582047372781791, 360582049827429793, 360582052281891290, 360582054906897923, 360582058674149125, 360582063467193021, 360582068259904516]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360677803186257643, 360677806539842546⟩, ⟨(-2282530190599074024), (-2282476079163812082)⟩, true⟩

def words04 : List Nat := [360582072161248081, 360582076891887260, 360582082952946085, 360582089013587024, 360582094195895031, 360582097633004049, 360582100187620405, 360582102742058364, 360582105236375845, 360582109249197969]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk238A

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk569A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk569B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk569A

def state06 : KState := ⟨⟨360610446749022833, 360610467319069605⟩, ⟨(-1630093746531739624), (-1629302143310462010)⟩, true⟩

def words05 : List Nat := [360581860084631386, 360581860614719820, 360581861215867845, 360581861510015098, 360581861543277905, 360581861576602144, 360581861917893432, 360581862494067414, 360581862996911811, 360581863499907188]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360620600770714977, 360620621348326740⟩, ⟨(-2208610725694056484), (-2207818691533766146)⟩, true⟩

def words06 : List Nat := [360581863849085638, 360581864065558453, 360581864589946038, 360581865114548378, 360581865560296204, 360581866139302761, 360581866507244405, 360581866875257932, 360581867289284587, 360581867970440908]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586497701656714, 360586518286754986⟩, ⟨(-265546796178322697), (-264754335475123089)⟩, true⟩

def words07 : List Nat := [360581868796108308, 360581869621897870, 360581870211805098, 360581870587741102, 360581870807059267, 360581871026578925, 360581871483743402, 360581871760415041, 360581871842678912, 360581871925064684]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360613006347233866, 360613026939816237⟩, ⟨(-1776146594452824779), (-1775353707267546969)⟩, true⟩

def words08 : List Nat := [360581872142336816, 360581872513267628, 360581873191787672, 360581873870438133, 360581874270510924, 360581874363872100, 360581874445739633, 360581874527834014, 360581874917459131, 360581875464894451]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360618296070894933, 360618316671039834⟩, ⟨(-2077640757315718977), (-2076847439105632489)⟩, true⟩

def words09 : List Nat := [360581875765885453, 360581876066951564, 360581876675593493, 360581877549121068, 360581878343979403, 360581879138939499, 360581879777902343, 360581880110266865, 360581880750146853, 360581881390270977]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk569B

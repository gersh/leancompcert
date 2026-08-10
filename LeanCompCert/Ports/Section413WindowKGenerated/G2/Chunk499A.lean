import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk499A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581459627059223, 360581475245288048⟩, ⟨21344402336480889, 21871016107131769⟩, true⟩

def state01 : KState := ⟨⟨360591418718429062, 360591434343162977⟩, ⟨(-475668973732502227), (-475142035325375137)⟩, true⟩

def words00 : List Nat := [360581913840954899, 360581914350776478, 360581914851584495, 360581915352494653, 360581915516120852, 360581915516809419, 360581915279890668, 360581914902926576, 360581914525776347, 360581914557237523]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584566798840346, 360584582430131997⟩, ⟨(-133731573387041975), (-133204307650185931)⟩, true⟩

def words01 : List Nat := [360581914557851014, 360581914515332907, 360581914472684385, 360581914609345766, 360581914631638424, 360581914654042461, 360581914654666641, 360581914366640728, 360581914073821120, 360581914128061723]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591540364137170, 360591556001910708⟩, ⟨(-481879909095852957), (-481352319750299393)⟩, true⟩

def words02 : List Nat := [360581914582322305, 360581914738602509, 360581914739222635, 360581914661167785, 360581914582992503, 360581914453011952, 360581914909891462, 360581915366884671, 360581915458042138, 360581915651832595]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608670239306904, 360608685883594997⟩, ⟨(-1337466432799871834), (-1336938518151495174)⟩, true⟩

def words03 : List Nat := [360581915828482391, 360581916005325959, 360581916113824915, 360581916114513998, 360581915823125478, 360581915186979714, 360581914550727526, 360581914450810207, 360581914987439347, 360581915524207891]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612641765642268, 360612657416493011⟩, ⟨(-1536033230012198044), (-1535504987593725976)⟩, true⟩

def words04 : List Nat := [360581915834406899, 360581915835096094, 360581916055085868, 360581916365540643, 360581916393522064, 360581916507562016, 360581916508175963, 360581916421924889, 360581916575105383, 360581917191320468]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk499A

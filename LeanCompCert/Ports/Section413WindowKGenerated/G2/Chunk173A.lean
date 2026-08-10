import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk173A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360661169634568037, 360661171349037595⟩, ⟨(-1336585116706725498), (-1336565038738940094)⟩, true⟩

def state01 : KState := ⟨⟨360592175199978168, 360592176916534756⟩, ⟨(-143166062235061452), (-143145948151159116)⟩, true⟩

def words00 : List Nat := [360583920255107588, 360583921046775670, 360583921046955140, 360583920842175664, 360583920637358166, 360583919561910293, 360583917442861481, 360583913618058390, 360583909793655854, 360583907842064699]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360554664931951721, 360554666650576920⟩, ⟨506272514072331184, 506292663974312430⟩, true⟩

def words01 : List Nat := [360583908232127486, 360583908622184032, 360583908622379634, 360583907011166457, 360583904956346861, 360583902034420237, 360583899510636475, 360583900016051301, 360583900016247096, 360583898328635484]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603907003520473, 360603908724217078⟩, ⟨(-346582756380374074), (-346562570591518474)⟩, true⟩

def words02 : List Nat := [360583898272217103, 360583901555348489, 360583905908868055, 360583910261926521, 360583911150215042, 360583911150434592, 360583909655081550, 360583910565702302, 360583910883794216, 360583912037898256]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556882527851384, 360556884250641121⟩, ⟨468836801640173867, 468857023713357429⟩, true⟩

def words03 : List Nat := [360583912038093968, 360583911312485568, 360583913176178192, 360583917531633200, 360583921021317860, 360583924510637133, 360583926327036229, 360583926327255942, 360583924853868894, 360583923294684568]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599735800370496, 360599737525229742⟩, ⟨(-274221228701767331), (-274200970733123091)⟩, true⟩

def words04 : List Nat := [360583923487842222, 360583926453627435, 360583927182498678, 360583927911307993, 360583927911492025, 360583930385393303, 360583931957998094, 360583933530461971, 360583933530657836, 360583934345543665]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk173A

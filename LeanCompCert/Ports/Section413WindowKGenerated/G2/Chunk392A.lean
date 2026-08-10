import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk392A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582395956352403, 360582405405976636⟩, ⟨(-4648617076317925), (-4398244791980945)⟩, true⟩

def state01 : KState := ⟨⟨360576532732382131, 360576542187053986⟩, ⟨225034164522323682, 225284734698352046⟩, true⟩

def words00 : List Nat := [360582293209188889, 360582292853135419, 360582292284756704, 360582292252396782, 360582292219888400, 360582292022739571, 360582291177938616, 360582289829184432, 360582288480394649, 360582287780899902]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360544029252407813, 360544038712071350⟩, ⟨1499808224680231039, 1500058990605514847⟩, true⟩

def words01 : List Nat := [360582287989826776, 360582288345367169, 360582288374564361, 360582288419016779, 360582288419464625, 360582287898033735, 360582287503272102, 360582287503802563, 360582286983803329, 360582286009129115]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595368015053530, 360595377479730574⟩, ⟨(-514105992690591368), (-513855030110371458)⟩, true⟩

def words02 : List Nat := [360582285034393653, 360582283779923456, 360582282854154885, 360582282377726460, 360582281901281490, 360582280871172411, 360582279744127767, 360582279265788813, 360582278956874260, 360582279291305340]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592960067791099, 360592969537525618⟩, ⟨(-419637104523282648), (-419385943513682976)⟩, true⟩

def words03 : List Nat := [360582279292332938, 360582279293413652, 360582279942743585, 360582281003869739, 360582281508026714, 360582282012237286, 360582282012713861, 360582281924720607, 360582281821738778, 360582282094710357]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603166410193437, 360603175884932920⟩, ⟨(-820101330747524383), (-819849973318446963)⟩, true⟩

def words04 : List Nat := [360582283015595325, 360582283951194698, 360582284504674248, 360582285058183561, 360582285333902541, 360582285982556629, 360582286822038516, 360582287661580781, 360582287986973317, 360582288519685705]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk392A

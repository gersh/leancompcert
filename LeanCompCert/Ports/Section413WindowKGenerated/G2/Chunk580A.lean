import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk580A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571411312890724, 360571432671983322⟩, ⟨608672065314417176, 609509024186479858⟩, true⟩

def state01 : KState := ⟨⟨360590935953082344, 360590957319830347⟩, ⟨(-523792529188699532), (-522955126265023966)⟩, true⟩

def words00 : List Nat := [360581941267734904, 360581941493808361, 360581941766924704, 360581942040184478, 360581942058786040, 360581942146746956, 360581942235735115, 360581942324956000, 360581942405593317, 360581942561831605]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581503561648811, 360581524936106208⟩, ⟨23484407671181163, 24322257854854709⟩, true⟩

def words01 : List Nat := [360581942562553264, 360581942544330117, 360581942804097486, 360581943305527575, 360581943671576993, 360581944037760378, 360581944240233611, 360581944241043635, 360581944147127830, 360581944140826216]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577252737479570, 360577274119575048⟩, ⟨270044745981909560, 270883039365084556⟩, true⟩

def words02 : List Nat := [360581944225319343, 360581944226129539, 360581944115679070, 360581943772897417, 360581943430000827, 360581942885404671, 360581942521573590, 360581942454950547, 360581942388242994, 360581942102331641]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601248961124276, 360601270350864385⟩, ⟨(-1122587509650342961), (-1121748772611192345)⟩, true⟩

def words03 : List Nat := [360581942239120014, 360581942456591178, 360581942907171479, 360581943061706550, 360581943062453907, 360581942960342499, 360581942858085437, 360581942849368583, 360581943183026861, 360581943516857198]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582152705930499, 360582174103394258⟩, ⟨(-14298544007938093), (-13459358651423859)⟩, true⟩

def words04 : List Nat := [360581943702448944, 360581943703259278, 360581943778217096, 360581943964702990, 360581943965386064, 360581943932151108, 360581943602715980, 360581943051319839, 360581942499787529, 360581942249358128]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk580A

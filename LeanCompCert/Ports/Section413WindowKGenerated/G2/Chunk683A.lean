import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk683A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589104476115736, 360589134483063198⟩, ⟨(-431645342089573277), (-430260964267621339)⟩, true⟩

def state01 : KState := ⟨⟨360617121408251717, 360617151424407051⟩, ⟨(-2345456518890316365), (-2344071512128615195)⟩, true⟩

def words00 : List Nat := [360582835001284566, 360582835006326336, 360582835198440357, 360582835390832032, 360582835481429397, 360582835705755923, 360582835822741131, 360582835939828249, 360582836220355696, 360582836723815220]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585939152511237, 360585969177763119⟩, ⟨(-215167213390653479), (-213781585196374545)⟩, true⟩

def words01 : List Nat := [360582837440881929, 360582838158112587, 360582838708900268, 360582839045746033, 360582839266066897, 360582839486633340, 360582839854487754, 360582840008512501, 360582840055182688, 360582840102000230]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592649422272441, 360592679456640454⟩, ⟨(-673658656651128989), (-672272405598122169)⟩, true⟩

def words02 : List Nat := [360582840181391821, 360582840391929004, 360582840675135625, 360582840958520465, 360582841057897326, 360582841058863258, 360582840999817421, 360582840876697492, 360582840842943423, 360582840987927892]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588950942531800, 360588980986095022⟩, ⟨(-420917836038421336), (-419530956631689674)⟩, true⟩

def words03 : List Nat := [360582841025624093, 360582841063431069, 360582841202582233, 360582841504663673, 360582841722077399, 360582841939642232, 360582842048541921, 360582842049508306, 360582842106490956, 360582842197423044]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360565560711350305, 360565590764023278⟩, ⟨1177580182917858773, 1178967684931753471⟩, true⟩

def words04 : List Nat := [360582842199106788, 360582842200072937, 360582841987978409, 360582841604970284, 360582841221815854, 360582840784823130, 360582840454500770, 360582840252906537, 360582840051196068, 360582839742588483]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk683A

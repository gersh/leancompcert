import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk688A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565027487324011, 360565057952909250⟩, ⟨1218705397845494491, 1220121215398078613⟩, true⟩

def state01 : KState := ⟨⟨360575438327663938, 360575468802442493⟩, ⟨502398566242560203, 503815016341048107⟩, true⟩

def words00 : List Nat := [360582792015924817, 360582791943250320, 360582791956046330, 360582791969014635, 360582791969926641, 360582791775023368, 360582791368973766, 360582791125585779, 360582790881922942, 360582790630902616]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582602032262560, 360582632516306509⟩, ⟨9419465537520080, 10836553233634472⟩, true⟩

def words01 : List Nat := [360582790525364842, 360582790314393832, 360582790103242681, 360582790207398507, 360582790259471579, 360582790311712372, 360582790312595516, 360582790191983991, 360582789979750300, 360582789978573781]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587897854160467, 360587928347365142⟩, ⟨(-355036383804201378), (-353618665619260928)⟩, true⟩

def words02 : List Nat := [360582790185505308, 360582790334649564, 360582790376840644, 360582790419144637, 360582790419960352, 360582790502980354, 360582790630521276, 360582790758239540, 360582790780388891, 360582790856036827]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589434462555527, 360589464964966977⟩, ⟨(-460865988489335343), (-459447636556592921)⟩, true⟩

def words03 : List Nat := [360582790927238897, 360582790998720693, 360582791141837938, 360582791142811500, 360582791128443805, 360582790930764259, 360582790732905826, 360582790728556708, 360582790826298434, 360582790924256404]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566713949667649, 360566744461358739⟩, ⟨1103221019660185811, 1104640010446868845⟩, true⟩

def words04 : List Nat := [360582790925132095, 360582790917184783, 360582790698347082, 360582790615151703, 360582790531715340, 360582790306159906, 360582789968635308, 360582789509706708, 360582789050605762, 360582788615468353]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk688A

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk442A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569165427526954, 360569177559979834⟩, ⟨622215682126216659, 622578073917619275⟩, true⟩

def state01 : KState := ⟨⟨360633743651848883, 360633755789997285⟩, ⟨(-2232374251336664471), (-2232011607774304585)⟩, true⟩

def words00 : List Nat := [360583262911244045, 360583263399841810, 360583264399530689, 360583265399290255, 360583265910175498, 360583266332691673, 360583267266280148, 360583268200009582, 360583269211498789, 360583270354070156]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360580388131641664, 360580400275550263⟩, ⟨126800255012104509, 127163153261232729⟩, true⟩

def words01 : List Nat := [360583271239483378, 360583272124932987, 360583272934060303, 360583274000861097, 360583274813423055, 360583275626046578, 360583276084412237, 360583276085016521, 360583276033088679, 360583275968749296]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581594453171411, 360581606602767772⟩, ⟨73430722585896492, 73793872375890646⟩, true⟩

def words02 : List Nat := [360583276350068836, 360583276350673157, 360583276286873194, 360583275966300215, 360583275645644317, 360583275048486490, 360583275023671894, 360583275182241506, 360583275182780649, 360583275014985179]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576319191316239, 360576331346625509⟩, ⟨306717516851323384, 307080919351248682⟩, true⟩

def words03 : List Nat := [360583275018195464, 360583275059299583, 360583275059796902, 360583274955206552, 360583274683943474, 360583273975884590, 360583273267742400, 360583272857780814, 360583272753329747, 360583272597062925]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575935741450115, 360575947902510628⟩, ⟨323529997970165534, 323893654933806296⟩, true⟩

def words04 : List Nat := [360583272440705174, 360583272027857142, 360583271543566950, 360583271461726681, 360583271379724005, 360583271167952570, 360583270446552929, 360583269305310964, 360583268164004850, 360583267533130602]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk442A

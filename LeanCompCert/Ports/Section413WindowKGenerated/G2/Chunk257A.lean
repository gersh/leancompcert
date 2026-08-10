import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk257A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591404017865555, 360591407937584289⟩, ⟨(-209415030629418661), (-209346886250479355)⟩, true⟩

def state01 : KState := ⟨⟨360546502109026749, 360546506031950932⟩, ⟨944534939913512492, 944603166688255028⟩, true⟩

def words00 : List Nat := [360583262461590827, 360583261839778530, 360583260232482304, 360583260135895549, 360583260039216716, 360583259198544406, 360583256852166953, 360583253152202670, 360583249452462201, 360583246722992872]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557910787238886, 360557914713337549⟩, ⟨651064426631464504, 651132735038084446⟩, true⟩

def words01 : List Nat := [360583245294282802, 360583243822680266, 360583242351158373, 360583240130368005, 360583238327074623, 360583235754823375, 360583233182673996, 360583232119642747, 360583231900089603, 360583230916099528]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586705510709473, 360586709439987452⟩, ⟨(-89664813793149931), (-89596423598802005)⟩, true⟩

def words02 : List Nat := [360583229932110882, 360583229317669185, 360583230199028194, 360583231080382759, 360583231080699100, 360583230532827453, 360583229342675748, 360583228577292542, 360583227811872364, 360583227397952600]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576295082291305, 360576299014785609⟩, ⟨178355382328896629, 178423855294945123⟩, true⟩

def words03 : List Nat := [360583227398255860, 360583226753275309, 360583226969721750, 360583228583762561, 360583229810864499, 360583231037925899, 360583231284067410, 360583231284405290, 360583231057414078, 360583230788495592]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360615040613484009, 360615044549148495⟩, ⟨(-819204707480366259), (-819136152897643025)⟩, true⟩

def words04 : List Nat := [360583231755945266, 360583232035147868, 360583232035448251, 360583231551788679, 360583231068112502, 360583229842930912, 360583231260573882, 360583232722061659, 360583233436065393, 360583234671749651]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk257A

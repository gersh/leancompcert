import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk664A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556778241351091, 360556806538525135⟩, ⟨1734154190424146879, 1735423406898457549⟩, true⟩

def state01 : KState := ⟨⟨360570509890045492, 360570538196076192⟩, ⟨822389643357027681, 823659447955080025⟩, true⟩

def words00 : List Nat := [360582942040358576, 360582941755231636, 360582941805903025, 360582941944952936, 360582941945818438, 360582941895447865, 360582941618595955, 360582941376877490, 360582941134905038, 360582940837966798]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569325009883587, 360569353324840896⟩, ⟨901090162547832100, 902360560005235634⟩, true⟩

def words01 : List Nat := [360582940652053535, 360582940327839128, 360582940003455187, 360582939920432785, 360582939921217123, 360582939826007273, 360582939730685913, 360582939484370815, 360582939203705197, 360582939000239952]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570930909634977, 360570959233426859⟩, ⟨794348763577899957, 795619747871525721⟩, true⟩

def words02 : List Nat := [360582938796458496, 360582938770792967, 360582938518839139, 360582938090551839, 360582937662122277, 360582937174089204, 360582936799432892, 360582936611106376, 360582936422697063, 360582936047334304]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584837258347554, 360584865590976063⟩, ⟨(-129495784599782235), (-128224213244396895)⟩, true⟩

def words03 : List Nat := [360582935913636123, 360582935960500971, 360582936144803506, 360582936184340893, 360582936185205343, 360582936021922638, 360582935858476151, 360582935690477396, 360582935665056165, 360582935695079789]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559682728023884, 360559711069569353⟩, ⟨1541738304964121737, 1543010468806153081⟩, true⟩

def words04 : List Nat := [360582935695914655, 360582935612857899, 360582935358566449, 360582935070792499, 360582934782760771, 360582934390089347, 360582933771331796, 360582933003426090, 360582932235364090, 360582931693629642]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk664A

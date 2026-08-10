import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk580A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476486542085729, 362476535732771168⟩, ⟨488048591164977377, 489975846455953805⟩, true⟩

def state01 : KState := ⟨⟨362483055436712640, 362483104644943301⟩, ⟨107095498006722271, 109023771011610593⟩, true⟩

def words00 : List Nat := [371284983549806161, 371284983552000901, 371284983690015028, 371284983836228220, 371284983932323823, 371284983934294296, 371284983844786518, 371284983881414224, 371284984039072349, 371284984041099337]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484880790776454, 362484930016829111⟩, ⟨1245832232947991, 3175139182591835⟩, true⟩

def words01 : List Nat := [371284984010166611, 371284983965305921, 371284984170133335, 371284984323593468, 371284984528574217, 371284984734363140, 371284984934478135, 371284984936436704, 371284984740277816, 371284984741737464]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472731233052532, 362472780476562343⟩, ⟨706217703647935129, 708148023552986651⟩, true⟩

def words02 : List Nat := [371284984926305680, 371284984928264736, 371284984762221241, 371284984537435000, 371284984311900888, 371284984094340369, 371284983762182857, 371284983728103098, 371284983693384795, 371284983613277025]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496081070617031, 362496130331854007⟩, ⟨(-648867975357835619), (-646936626658582723)⟩, true⟩

def words03 : List Nat := [371284983491292411, 371284983580667076, 371284983941034642, 371284983942993828, 371284983907622965, 371284983837196897, 371284983815482631, 371284983817647353, 371284983937033106, 371284984131294772]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479623070401695, 362479672349336090⟩, ⟨306382132828528365, 308314508775759089⟩, true⟩

def words04 : List Nat := [371284984325890608, 371284984327850146, 371284984220917834, 371284984317692875, 371284984450483888, 371284984452443650, 371284984189583907, 371284983873647653, 371284983556897945, 371284983538117757]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk580A

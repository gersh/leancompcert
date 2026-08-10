import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk586A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570230044981887, 360570251866272726⟩, ⟨688635210183269646, 689499115429808678⟩, true⟩

def state01 : KState := ⟨⟨360599261971324165, 360599283800340046⟩, ⟨(-1012686639573703135), (-1011822281601383435)⟩, true⟩

def words00 : List Nat := [360582017953099940, 360582018189875178, 360582018717611822, 360582019245506827, 360582019526536254, 360582019527354769, 360582019724382087, 360582019931804991, 360582020153671219, 360582020449064665]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597509519906649, 360597531356728010⟩, ⟨(-909969441563598403), (-909104626072943869)⟩, true⟩

def words01 : List Nat := [360582020522053706, 360582020595117016, 360582020959153264, 360582021468735762, 360582021839901387, 360582022211188712, 360582022390971429, 360582022652726454, 360582022917956248, 360582023183444154]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589619407394656, 360589641251922507⟩, ⟨(-447524229974838318), (-446658962690964542)⟩, true⟩

def words02 : List Nat := [360582023560897949, 360582023648235548, 360582023648964889, 360582023589949313, 360582023530815015, 360582023251908057, 360582023123630776, 360582023127303089, 360582023128032472, 360582023115395910]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360614406085277848, 360614427937537143⟩, ⟨(-1900876991127239857), (-1900011270510047725)⟩, true⟩

def words03 : List Nat := [360582023536936100, 360582023958717765, 360582024476183730, 360582024869856493, 360582025015920044, 360582025162035555, 360582025538073083, 360582026099857249, 360582026653085986, 360582027206469971]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612218809207618, 360612240669266600⟩, ⟨(-1772815698170014433), (-1771949520142147007)⟩, true⟩

def words04 : List Nat := [360582027541441376, 360582027656121139, 360582027838141294, 360582028020401687, 360582028063832504, 360582028206480141, 360582028207209806, 360582028197317356, 360582028400294497, 360582028916352888]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk586A

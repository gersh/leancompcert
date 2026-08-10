import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk577A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474127833095285, 362474176496147053⟩, ⟨620819627888999847, 622716359458860165⟩, true⟩

def state01 : KState := ⟨⟨362487347664312501, 362487396344814595⟩, ⟨(-142031418726928207), (-140133680184518607)⟩, true⟩

def words00 : List Nat := [371284968621708309, 371284968560532626, 371284968380288849, 371284968402051180, 371284968403558158, 371284968378903133, 371284968138960531, 371284968028194059, 371284968103667304, 371284968147760576]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 57700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 57700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483438283277358, 362483486981524567⟩, ⟨83629342763768673, 85528105465485053⟩, true⟩

def words01 : List Nat := [371284968190095498, 371284968233111034, 371284968575677499, 371284968769776473, 371284968898396585, 371284969027712630, 371284969103386234, 371284969105333932, 371284968780663714, 371284968757433533]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 57710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 57700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491740597869765, 362491789313496033⟩, ⟨(-395555107513602281), (-393655341604191203)⟩, true⟩

def words02 : List Nat := [371284968996077292, 371284969093359400, 371284969180597657, 371284969268471943, 371284969446094690, 371284969475689221, 371284969804668984, 371284970134472232, 371284970407239843, 371284970527374120]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 57720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 57700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508701725392635, 362508750458592642⟩, ⟨(-1374768299141448996), (-1372867518608322606)⟩, true⟩

def words03 : List Nat := [371284970947009851, 371284971367624824, 371284971985545551, 371284972204087035, 371284972372119887, 371284972540792960, 371284973008748558, 371284973328389593, 371284973741518137, 371284974155469934]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 57730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 57700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485605955173726, 362485654705991828⟩, ⟨(-41167021791235164), (-39265223901750374)⟩, true⟩

def words04 : List Nat := [371284974558694703, 371284974562508994, 371284974673779710, 371284974786080349, 371284974988004490, 371284974989962298, 371284974905834651, 371284974821066143, 371284974786416011, 371284974800468084]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 57740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 57700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk577A

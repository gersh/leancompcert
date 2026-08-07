import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk577

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

def state06 : KState := ⟨⟨362467250591504702, 362467299359860518⟩, ⟨1019055311223170982, 1020958122006271580⟩, true⟩

def words05 : List Nat := [371284975113585513, 371284975427501308, 371284975724033069, 371284975725982077, 371284975698206538, 371284975731263117, 371284975830150792, 371284975832099663, 371284975531430162, 371284975227623785]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476484464775742, 362476533250565535⟩, ⟨485667416000454043, 487571233859309771⟩, true⟩

def words06 : List Nat := [371284974922938195, 371284974713435578, 371284974352921964, 371284974244588243, 371284974135633461, 371284973981002487, 371284973520691482, 371284973313129128, 371284973117577279, 371284973119595470]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485384245589875, 362485433049167435⟩, ⟨(-28513593614306549), (-26608748067597359)⟩, true⟩

def words07 : List Nat := [371284972975000977, 371284972772840996, 371284972665419328, 371284972667567345, 371284972652765528, 371284972692101076, 371284972729430927, 371284972731414413, 371284972528438875, 371284972538825496]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473699771843622, 362473748592759840⟩, ⟨646696644768972577, 648602492234903713⟩, true⟩

def words08 : List Nat := [371284972847836846, 371284972849786610, 371284972799677929, 371284972649259513, 371284972498112180, 371284972344001488, 371284972040198246, 371284972036845619, 371284972032866827, 371284972030936600]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362505329522319881, 362505378360932126⟩, ⟨(-1181282272705609205), (-1179375402503433689)⟩, true⟩

def words09 : List Nat := [371284971943491644, 371284972051330685, 371284972457715259, 371284972649005875, 371284972793941449, 371284972939460923, 371284973304642026, 371284973585614956, 371284973939987179, 371284974295215211]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk577

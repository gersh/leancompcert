import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk558A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474607053662095, 362474652443659719⟩, ⟨571656488676864080, 573367455297019514⟩, true⟩

def state01 : KState := ⟨⟨362463900440580645, 362463945847301823⟩, ⟨1169144762699543969, 1170856662580776699⟩, true⟩

def words00 : List Nat := [371284927720214275, 371284927722092272, 371284927352837540, 371284926918891706, 371284926484224820, 371284926148474471, 371284925668595756, 371284925510124661, 371284925351020493, 371284925181875928]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496271210919612, 362496316634610343⟩, ⟨(-637689100845316288), (-635976253805096798)⟩, true⟩

def words01 : List Nat := [371284924807277097, 371284924462849301, 371284924117481713, 371284924093293333, 371284923836860714, 371284923519046568, 371284923201125506, 371284923203251009, 371284923292249634, 371284923498446443]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488452124439707, 362488497565072440⟩, ⟨(-201223479347328378), (-199509686517251182)⟩, true⟩

def words02 : List Nat := [371284923674529890, 371284923676421765, 371284923917104936, 371284924199304349, 371284924415083151, 371284924416962176, 371284924243855477, 371284924070608197, 371284924041766785, 371284924107915713]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471592790116278, 362471638247714725⟩, ⟨740199978317906290, 741914718429485740⟩, true⟩

def words03 : List Nat := [371284924442426418, 371284924777740277, 371284925082916510, 371284925084795732, 371284924962664915, 371284924899652220, 371284925090703044, 371284925092582359, 371284924921886341, 371284924686082016]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491839852875734, 362491885327291741⟩, ⟨(-390451742920851286), (-388736063630836638)⟩, true⟩

def words04 : List Nat := [371284924449426480, 371284924451472235, 371284924489468054, 371284924669976035, 371284924779323981, 371284924781236283, 371284924630024979, 371284924638468297, 371284924966102570, 371284925092674083]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk558A

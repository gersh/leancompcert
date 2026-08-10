import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk613A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567703816864140, 360567727780768140⟩, ⟨905301932622032732, 906294310703365850⟩, true⟩

def state01 : KState := ⟨⟨360609355559783962, 360609379531795683⟩, ⟨(-1648163239096230225), (-1647170363972472259)⟩, true⟩

def words00 : List Nat := [360582512113051076, 360582512180863630, 360582512350946513, 360582512521184005, 360582512521976282, 360582512465759500, 360582512682642729, 360582512899784362, 360582513271503747, 360582513710589497]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601673035419579, 360601697015624224⟩, ⟨(-1177153242784413925), (-1176159865312727979)⟩, true⟩

def words01 : List Nat := [360582514001925550, 360582514293346053, 360582514495899624, 360582514903761680, 360582515243534623, 360582515583436828, 360582515787669946, 360582516011870663, 360582516325368932, 360582516639157554]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568662338828529, 360568686327117892⟩, ⟨847163869878241326, 848157743146934728⟩, true⟩

def words02 : List Nat := [360582516940401732, 360582516976949112, 360582516977714570, 360582516880782295, 360582516783718563, 360582516497270979, 360582516345997338, 360582516187678530, 360582516029270911, 360582515737571943]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360631062898877495, 360631086895279427⟩, ⟨(-2980184390987643955), (-2979190020135117557)⟩, true⟩

def words03 : List Nat := [360582515552931027, 360582515594031135, 360582515900500197, 360582516325863865, 360582516517379704, 360582516708956608, 360582517103548427, 360582517630744120, 360582518423243029, 360582519215911059]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614095942832309, 360614119947432205⟩, ⟨(-1939490449179251641), (-1938495575423823581)⟩, true⟩

def words04 : List Nat := [360582519783269646, 360582520086009874, 360582520654116742, 360582521222467232, 360582521722862593, 360582522073840892, 360582522205395432, 360582522337046050, 360582522626557814, 360582523142564741]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk613A

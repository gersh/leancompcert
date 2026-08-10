import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk928A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485655887187579, 362485786508989921⟩, ⟨(-70101499435612674), (-61917264154080642)⟩, true⟩

def state01 : KState := ⟨⟨362490495874700148, 362490626525540388⟩, ⟨(-519246164570073915), (-511059234419944555)⟩, true⟩

def words00 : List Nat := [371285119429792476, 371285119498787789, 371285119619964985, 371285119742425333, 371285119836217635, 371285119839521394, 371285119854695225, 371285119876037369, 371285120011734503, 371285120074425543]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492358315848430, 362492488996283601⟩, ⟨(-692115112306823140), (-683925435305714306)⟩, true⟩

def words01 : List Nat := [371285120135890483, 371285120198421611, 371285120308072407, 371285120368788817, 371285120454805594, 371285120542102438, 371285120628825596, 371285120632094180, 371285120694036491, 371285120777504384]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478552843018880, 362478683552328778⟩, ⟨589423463741847341, 597615821045875187⟩, true⟩

def words02 : List Nat := [371285120975160665, 371285121019174677, 371285121062084076, 371285121106120561, 371285121175807842, 371285121190949586, 371285121237959687, 371285121286228206, 371285121293457427, 371285121296819201]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494936754141661, 362495067492836408⟩, ⟨(-931565922515556755), (-923370837267745601)⟩, true⟩

def words03 : List Nat := [371285121276374811, 371285121327011128, 371285121430823202, 371285121461254769, 371285121471391842, 371285121482487566, 371285121544494838, 371285121550015640, 371285121659347353, 371285121770178663]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489668849000887, 362489799617017113⟩, ⟨(-442517034027692134), (-434319226422012512)⟩, true⟩

def words04 : List Nat := [371285121857158619, 371285121860406914, 371285121856423752, 371285121908222671, 371285121985878001, 371285121989141417, 371285121955804221, 371285121923387518, 371285121969511577, 371285122023599466]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk928A

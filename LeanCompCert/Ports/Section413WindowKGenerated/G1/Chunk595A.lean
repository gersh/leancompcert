import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk595A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487516452294864, 362487568325335059⟩, ⟨(-150280517389586093), (-148195664301362621)⟩, true⟩

def state01 : KState := ⟨⟨362495347562635166, 362495399453685494⟩, ⟨(-616258590375058147), (-614172665593028381)⟩, true⟩

def words00 : List Nat := [371285077854005406, 371285077907571709, 371285078212742407, 371285078518747539, 371285078781702972, 371285078783715936, 371285078669820784, 371285078672210865, 371285078956450989, 371285079131970299]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502767185592472, 362502819094994834⟩, ⟨(-1057796266872427738), (-1055709249871113242)⟩, true⟩

def words01 : List Nat := [371285079302412332, 371285079473546438, 371285079926742139, 371285080313042775, 371285080782963421, 371285081253620729, 371285081686100099, 371285081742526776, 371285082041899709, 371285082342422278]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475929744585336, 362475981671938094⟩, ⟨539688810025314420, 541776895529114598⟩, true⟩

def words02 : List Nat := [371285082675813801, 371285082677827470, 371285082634837523, 371285082591095741, 371285082587133794, 371285082589373473, 371285082517801208, 371285082547561431, 371285082575204425, 371285082577288827]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502962253098425, 362503014198630130⟩, ⟨(-1069695525820191334), (-1067606358032707506)⟩, true⟩

def words03 : List Nat := [371285082500215541, 371285082577054673, 371285082873327271, 371285082896582420, 371285082898185010, 371285082851806618, 371285082963482868, 371285082984240231, 371285083286769051, 371285083590174903]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484342908251424, 362484394871964102⟩, ⟨38980541439328682, 41070791816019346⟩, true⟩

def words04 : List Nat := [371285083871555376, 371285083920214960, 371285084111361679, 371285084303576479, 371285084579152156, 371285084581170835, 371285084566298532, 371285084532460707, 371285084555504755, 371285084557804842]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk595A

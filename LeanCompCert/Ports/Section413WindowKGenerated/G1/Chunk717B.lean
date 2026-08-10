import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk717A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk717B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk717A

def state06 : KState := ⟨⟨362483142058165575, 362483218628732164⟩, ⟨142133984913933209, 145844803304132657⟩, true⟩

def words05 : List Nat := [371285250590005833, 371285250672950097, 371285250847739744, 371285250926246930, 371285251057234765, 371285251189139134, 371285251248227484, 371285251250688708, 371285251050877065, 371285251025656693]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479112681336959, 362479189273815742⟩, ⟨431335882211164051, 435048273134902969⟩, true⟩

def words06 : List Nat := [371285251164616319, 371285251167078253, 371285251105016420, 371285251036770262, 371285250967542641, 371285250950433767, 371285250882182244, 371285250931142753, 371285250972161237, 371285250974709360]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362496988425709794, 362497065040444049⟩, ⟨(-851733274337385902), (-848019286024854924)⟩, true⟩

def words07 : List Nat := [371285250891949513, 371285250891584938, 371285251014876832, 371285251017345347, 371285250945040946, 371285250811907528, 371285250735768041, 371285250738528192, 371285250893286009, 371285251060616172]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494768055844565, 362494844692776532⟩, ⟨(-692401586618699536), (-688686004839963824)⟩, true⟩

def words08 : List Nat := [371285251217278962, 371285251219746454, 371285251266968778, 371285251361893655, 371285251469238609, 371285251471729466, 371285251462017694, 371285251453559087, 371285251626799619, 371285251763233275]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468903919343180, 362468980578497806⟩, ⟨1164568111991102984, 1168285289246812486⟩, true⟩

def words09 : List Nat := [371285251967929215, 371285252173695512, 371285252376755498, 371285252379218164, 371285252323726828, 371285252320830080, 371285252377965094, 371285252380427975, 371285252185187846, 371285251961356397]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk717B

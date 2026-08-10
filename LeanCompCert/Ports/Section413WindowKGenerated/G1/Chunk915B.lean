import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk915A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk915B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk915A

def state06 : KState := ⟨⟨362477726111516360, 362477853133587848⟩, ⟨656349663361322055, 664202069653135263⟩, true⟩

def words05 : List Nat := [371285107590271884, 371285107639006770, 371285107665395397, 371285107668921151, 371285107637072028, 371285107641763366, 371285107644309606, 371285107647508879, 371285107490861830, 371285107415694152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465741651184521, 362465868701733790⟩, ⟨1753728735060885239, 1761583748927702041⟩, true⟩

def words06 : List Nat := [371285107338640154, 371285107329691146, 371285107198078024, 371285107058336772, 371285106917378421, 371285106814329124, 371285106650155040, 371285106523876750, 371285106396477785, 371285106265880648]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488438993597621, 362488566073025661⟩, ⟨(-324757985046447441), (-316900326603519761)⟩, true⟩

def words07 : List Nat := [371285106057966919, 371285105970888814, 371285105910467801, 371285105913726124, 371285105863054137, 371285105769617174, 371285105697093217, 371285105700619896, 371285105703361843, 371285105744719533]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486335478488685, 362486462586848613⟩, ⟨(-132150019806144483), (-124289711640300893)⟩, true⟩

def words08 : List Nat := [371285105759945131, 371285105763148202, 371285105652198298, 371285105659140097, 371285105684699415, 371285105687926312, 371285105631461398, 371285105575944477, 371285105560467268, 371285105578936916]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362480243703994358, 362480370841181211⟩, ⟨425874679234334510, 433737627805880286⟩, true⟩

def words09 : List Nat := [371285105715065587, 371285105852523110, 371285105989203597, 371285105992405841, 371285105991558511, 371285105996186822, 371285106059491631, 371285106062708121, 371285106016172351, 371285105968122324]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk915B

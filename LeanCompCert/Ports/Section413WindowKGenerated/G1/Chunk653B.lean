import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk653A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk653B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk653A

def state06 : KState := ⟨⟨362488131745266097, 362488194804760755⟩, ⟨(-178461371052996436), (-175677596206422788)⟩, true⟩

def words05 : List Nat := [371285507439668399, 371285507343579142, 371285507381404298, 371285507383631296, 371285507249044461, 371285507078277714, 371285506967410992, 371285506969886851, 371285506956504674, 371285507000164644]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490629652959979, 362490692732528902⟩, ⟨(-341780552211579613), (-338995465207247763)⟩, true⟩

def words06 : List Nat := [371285507042752354, 371285507044993611, 371285506913198640, 371285506951780932, 371285507008590768, 371285507010861929, 371285506940315505, 371285506868248751, 371285506934284973, 371285507016153029]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473128413319513, 362473191512954570⟩, ⟨802438136832799742, 805224535661335376⟩, true⟩

def words07 : List Nat := [371285507330809392, 371285507646342063, 371285507886536844, 371285507888763598, 371285507817117090, 371285507816998878, 371285507933171947, 371285507935398970, 371285507766960848, 371285507581104790]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483579572924821, 362483642692470262⟩, ⟨119154894682199370, 121942595355901074⟩, true⟩

def words08 : List Nat := [371285507439626268, 371285507442086977, 371285507553045160, 371285507714686240, 371285507836839715, 371285507839066988, 371285507649433265, 371285507558058991, 371285507540977232, 371285507543293873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484558343316369, 362484621483178746⟩, ⟨55178417549697308, 57967446847938548⟩, true⟩

def words09 : List Nat := [371285507516440940, 371285507481423778, 371285507641656900, 371285507760887333, 371285507841777016, 371285507923484282, 371285508004342463, 371285508006575023, 371285507846347392, 371285507835577033]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk653B

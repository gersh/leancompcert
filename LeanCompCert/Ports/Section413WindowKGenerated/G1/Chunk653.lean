import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk653

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491216794105905, 362491279733294307⟩, ⟨(-379238634720404714), (-376462719489524510)⟩, true⟩

def state01 : KState := ⟨⟨362467735297680904, 362467798256948763⟩, ⟨1154153207412836138, 1156930433935161262⟩, true⟩

def words00 : List Nat := [371285514785541435, 371285514787765868, 371285514590816742, 371285514460101264, 371285514328246670, 371285514234099392, 371285513827062327, 371285513374319820, 371285512920704551, 371285512702423196]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362459705774099917, 362459768753411474⟩, ⟨1678669645041947650, 1681448180719365064⟩, true⟩

def words01 : List Nat := [371285512432700295, 371285512377418312, 371285512321362347, 371285512228342093, 371285511911931714, 371285511668385841, 371285511423747700, 371285511242448807, 371285510850135138, 371285510458566394]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477802622006658, 362477865621236487⟩, ⟨496556804037171851, 499336640877311949⟩, true⟩

def words02 : List Nat := [371285510065995832, 371285509885969066, 371285509618082752, 371285509585267092, 371285509551748972, 371285509487839953, 371285509139382007, 371285509026236808, 371285508916665000, 371285508918969188]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486639551884247, 362486702571409776⟩, ⟨(-80832002229577275), (-78050839371222883)⟩, true⟩

def words03 : List Nat := [371285508803689206, 371285508612313993, 371285508435715241, 371285508438167386, 371285508338373899, 371285508300464168, 371285508261786260, 371285508207532151, 371285508034818490, 371285508055877856]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474474882157452, 362474537921480062⟩, ⟨714086426794344408, 716868883296500244⟩, true⟩

def words04 : List Nat := [371285508242355533, 371285508244582448, 371285508159930948, 371285508055206851, 371285507949629345, 371285507855354177, 371285507643200653, 371285507633958574, 371285507623993538, 371285507605998754]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk653

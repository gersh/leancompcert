import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk950A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk950B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk950A

def state06 : KState := ⟨⟨362485964193877214, 362486101510843280⟩, ⟨(-93917806228520569), (-85104660970883269)⟩, true⟩

def words05 : List Nat := [371285206448459674, 371285206492010256, 371285206562685106, 371285206566016481, 371285206489412610, 371285206397123867, 371285206303423978, 371285206292405001, 371285206233964557, 371285206247160268]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478983515373583, 362479120862360434⟩, ⟨569706204319103947, 578522203508299325⟩, true⟩

def words06 : List Nat := [371285206258701930, 371285206262059311, 371285206238319263, 371285206284723966, 371285206362758373, 371285206366090068, 371285206296828611, 371285206207875028, 371285206117607962, 371285206085916849]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475681047694546, 362475818424700193⟩, ⟨883737752217231110, 892556605446697818⟩, true⟩

def words07 : List Nat := [371285206070896356, 371285206121286086, 371285206137333351, 371285206140723652, 371285206064713087, 371285206024346158, 371285206030492574, 371285206033824861, 371285205947145458, 371285205852187012]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483862986657960, 362484000393546619⟩, ⟨105751960384995029, 114573655041577101⟩, true⟩

def words08 : List Nat := [371285205755762027, 371285205674970576, 371285205559168752, 371285205555430530, 371285205550684145, 371285205528307291, 371285205357401638, 371285205299045606, 371285205287087212, 371285205290539380]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485820623173871, 362485958060363817⟩, ⟨(-80402275822684006), (-71577699661356334)⟩, true⟩

def words09 : List Nat := [371285205280361133, 371285205265138900, 371285205340474027, 371285205381317791, 371285205411143828, 371285205442202518, 371285205471735272, 371285205475077481, 371285205399067316, 371285205411078727]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk950B

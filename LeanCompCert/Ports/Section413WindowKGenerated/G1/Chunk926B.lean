import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk926A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk926B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk926A

def state06 : KState := ⟨⟨362492759350498772, 362492889563148150⟩, ⟨(-728584402429530074), (-720438107934265616)⟩, true⟩

def words05 : List Nat := [371285113952546649, 371285114064078034, 371285114233291713, 371285114248301822, 371285114250835278, 371285114246169463, 371285114348364323, 371285114402073202, 371285114488222287, 371285114575743155]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486405450227463, 362486535692125177⟩, ⟨(-139846345396128315), (-131697340606487527)⟩, true⟩

def words06 : List Nat := [371285114654779201, 371285114658020039, 371285114613018640, 371285114635915396, 371285114683352373, 371285114686649750, 371285114637340032, 371285114569418119, 371285114545224574, 371285114564257706]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474421617243017, 362474551888376846⟩, ⟨970803110116101249, 978954824365759733⟩, true⟩

def words07 : List Nat := [371285114698210684, 371285114833527461, 371285114943550552, 371285114946791670, 371285114901451945, 371285114859513258, 371285114847554385, 371285114850795738, 371285114739488286, 371285114629252610]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489426435650117, 362489556735806657⟩, ⟨(-419884817602772335), (-411730413383446509)⟩, true⟩

def words08 : List Nat := [371285114519908730, 371285114523522395, 371285114561732911, 371285114641435736, 371285114690207766, 371285114693471511, 371285114639301838, 371285114635277906, 371285114716962691, 371285114768265219]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493981083266749, 362494111412919990⟩, ⟨(-842059641367696994), (-833902502948331680)⟩, true⟩

def words09 : List Nat := [371285114817351896, 371285114867478449, 371285115032676614, 371285115156984031, 371285115315603812, 371285115475491692, 371285115613713014, 371285115616955062, 371285115696891232, 371285115797954151]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk926B

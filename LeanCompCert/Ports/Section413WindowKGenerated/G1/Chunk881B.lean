import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk881A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk881B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk881A

def state06 : KState := ⟨⟨362488771162678516, 362488888582768693⟩, ⟨(-332258028803264489), (-325268568697364153)⟩, true⟩

def words05 : List Nat := [371285199570693040, 371285199493295944, 371285199418756673, 371285199421848520, 371285199313339278, 371285199187509618, 371285199060460023, 371285199060295307, 371285199053755549, 371285199099111551]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483491958740691, 362483609406507013⟩, ⟨133146771709022337, 140138671886447741⟩, true⟩

def words06 : List Nat := [371285199143302086, 371285199146381714, 371285199087996937, 371285199120980608, 371285199132695482, 371285199135781638, 371285199024389059, 371285198914120718, 371285198817450682, 371285198820955085]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472950124699748, 362473067600142825⟩, ⟨1062719528526798696, 1069713869102549464⟩, true⟩

def words07 : List Nat := [371285198887658165, 371285198973667138, 371285199040379209, 371285199043450958, 371285198938628304, 371285198873566113, 371285198866514303, 371285198869586088, 371285198760252256, 371285198626102256]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484597524247555, 362484715027154534⟩, ⟨35638887516205745, 42635650000615961⟩, true⟩

def words08 : List Nat := [371285198490615695, 371285198473921615, 371285198445740366, 371285198490659613, 371285198514085881, 371285198517211683, 371285198433422758, 371285198417293971, 371285198476179287, 371285198479360007]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486211351465550, 362486328882493132⟩, ⟨(-106715421103800268), (-99716178534360870)⟩, true⟩

def words09 : List Nat := [371285198476196998, 371285198459938942, 371285198463849767, 371285198467235865, 371285198426600413, 371285198416277420, 371285198404935304, 371285198394463331, 371285198309630884, 371285198326393606]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk881B

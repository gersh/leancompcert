import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk754A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk754B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk754A

def state06 : KState := ⟨⟨362477194971000643, 362477279972880542⟩, ⟨594152275020029771, 598483863113194891⟩, true⟩

def words05 : List Nat := [371285211269654443, 371285211387827614, 371285211470058425, 371285211472657661, 371285211356145651, 371285211294512847, 371285211316169652, 371285211318769301, 371285211215534188, 371285211113393572]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 75450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 75400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478680319072327, 362478765344158480⟩, ⟨482092530740173618, 486425870097774634⟩, true⟩

def words06 : List Nat := [371285211047841629, 371285211050703874, 371285211023887212, 371285211048113087, 371285211060921722, 371285211063519486, 371285210860620263, 371285210732373036, 371285210629267022, 371285210631956251]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 75460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 75400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487608530839780, 362487693579627583⟩, ⟨(-191773306357448337), (-187438178119692305)⟩, true⟩

def words07 : List Nat := [371285210548510581, 371285210431189223, 371285210346415461, 371285210349355344, 371285210345018754, 371285210371510464, 371285210398861843, 371285210401472228, 371285210293675830, 371285210329828035]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 75470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 75400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477106978527637, 362477192050483830⟩, ⟨600953160236504837, 605290037343829503⟩, true⟩

def words08 : List Nat := [371285210401025641, 371285210403642630, 371285210355195688, 371285210306878468, 371285210257592221, 371285210254120555, 371285210180458811, 371285210188888946, 371285210196387579, 371285210199077602]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 75480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 75400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485300645052774, 362485385740449931⟩, ⟨(-17642220382231715), (-13303573596359017)⟩, true⟩

def words09 : List Nat := [371285210104318573, 371285210117115014, 371285210219337801, 371285210221936452, 371285210090638619, 371285209917043024, 371285209742376271, 371285209680043996, 371285209531278357, 371285209536510959]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 75490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 75400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 75400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk754B

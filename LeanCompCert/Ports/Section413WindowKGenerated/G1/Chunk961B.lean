import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk961A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk961B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk961A

def state06 : KState := ⟨⟨362483122834929171, 362483263473162298⟩, ⟨184133158605844267, 193263854171051257⟩, true⟩

def words05 : List Nat := [371285272772835013, 371285272915544312, 371285273056586557, 371285273065689627, 371285273106312948, 371285273148605389, 371285273297421020, 371285273303110408, 371285273305680162, 371285273288617488]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362493288398122587, 362493429066528697⟩, ⟨(-793420696343340183), (-784287099188222737)⟩, true⟩

def words06 : List Nat := [371285273317267173, 371285273342323001, 371285273421879887, 371285273502776822, 371285273564743821, 371285273568175512, 371285273617588125, 371285273699344749, 371285273847280689, 371285273935572503]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493396896604577, 362493537595755638⟩, ⟨(-803869335412535657), (-794732781360211843)⟩, true⟩

def words07 : List Nat := [371285274022481821, 371285274110498864, 371285274209868004, 371285274270517282, 371285274362946321, 371285274456707947, 371285274548880167, 371285274552260612, 371285274618144345, 371285274708268919]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485249654532735, 362485390383692054⟩, ⟨(-20197402610240752), (-11057962207278802)⟩, true⟩

def words08 : List Nat := [371285274904690200, 371285274958054177, 371285275010918102, 371285275064952727, 371285275150146787, 371285275201621715, 371285275274266190, 371285275348201001, 371285275420617058, 371285275425305020]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499529965990873, 362499670725695534⟩, ⟨(-1393895359651018946), (-1384752980944218832)⟩, true⟩

def words09 : List Nat := [371285275517332071, 371285275611195976, 371285275765940555, 371285275831978438, 371285275868285242, 371285275905593665, 371285276003133585, 371285276048296929, 371285276200217197, 371285276353693744]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk961B

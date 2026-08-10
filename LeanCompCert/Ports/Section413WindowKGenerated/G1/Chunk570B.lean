import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk570A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk570B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk570A

def state06 : KState := ⟨⟨362495055384636090, 362495102932008143⟩, ⟨(-580800024633335087), (-578967311598202123)⟩, true⟩

def words05 : List Nat := [371284954731028264, 371284954840042216, 371284955194956796, 371284955406926801, 371284955710768894, 371284956015363502, 371284956237604834, 371284956239529207, 371284956289044005, 371284956469247270]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487294834946110, 362487342399447446⟩, ⟨(-137926027795493562), (-136092337273572398)⟩, true⟩

def words06 : List Nat := [371284956901734378, 371284956964632679, 371284957002943241, 371284957041952884, 371284957152321172, 371284957154441250, 371284957335415657, 371284957560894380, 371284957741107247, 371284957784892356]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362504828442922075, 362504876024857768⟩, ⟨(-1138674439372824527), (-1136839753786251907)⟩, true⟩

def words07 : List Nat := [371284957931534289, 371284958079172755, 371284958533092240, 371284958578366085, 371284958579857098, 371284958576512082, 371284958874250480, 371284959068478583, 371284959418723547, 371284959769820431]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495130988251985, 362495178587538362⟩, ⟨(-585191823930668513), (-583356147879019999)⟩, true⟩

def words08 : List Nat := [371284960110743078, 371284960112667565, 371284960177467283, 371284960312900685, 371284960451939668, 371284960453872634, 371284960363113012, 371284960274311379, 371284960400919818, 371284960582110554]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479932671889965, 362479980288505405⟩, ⟨282633611699309680, 284470277155611152⟩, true⟩

def words09 : List Nat := [371284960998949748, 371284961416574849, 371284961832161628, 371284961839263872, 371284961912400078, 371284961986532163, 371284962366654252, 371284962368579515, 371284962339935258, 371284962254830372]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk570B

import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk684A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk684B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk684A

def state06 : KState := ⟨⟨362482995592700728, 362483065027433229⟩, ⟨160507722398883973, 163718147262816727⟩, true⟩

def words05 : List Nat := [371285456430638553, 371285456493092315, 371285456575328767, 371285456577930927, 371285456592728533, 371285456634365244, 371285456668817989, 371285456671169060, 371285456501852144, 371285456469841392]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470726320130083, 362470795775672946⟩, ⟨1000552458125930931, 1003764307777751337⟩, true⟩

def words06 : List Nat := [371285456587435191, 371285456589775391, 371285456458286570, 371285456327405059, 371285456195582914, 371285456129717316, 371285455956218483, 371285455873111511, 371285455789239336, 371285455689617415]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495519856381181, 362495589333119947⟩, ⟨(-697196450959567466), (-693983149922089598)⟩, true⟩

def words07 : List Nat := [371285455477110826, 371285455347240664, 371285455296366834, 371285455298748969, 371285455236119194, 371285455115700117, 371285455084342274, 371285455086921807, 371285455230719469, 371285455381368044]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490803712598861, 362490873210492802⟩, ⟨(-374272762798963501), (-371058012945920855)⟩, true⟩

def words08 : List Nat := [371285455491005351, 371285455493346530, 371285455401553992, 371285455464110944, 371285455590513960, 371285455592871105, 371285455535077359, 371285455457494228, 371285455511594633, 371285455593390615]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475313087699011, 362475382606640015⟩, ⟨686839966708150668, 690056158182345986⟩, true⟩

def words09 : List Nat := [371285455886954704, 371285456181441868, 371285456451847411, 371285456492350169, 371285456535174205, 371285456579153871, 371285456685540999, 371285456687884596, 371285456563621810, 371285456419168225]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk684B

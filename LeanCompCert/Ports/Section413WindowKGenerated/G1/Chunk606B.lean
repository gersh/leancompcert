import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk606A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk606B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk606A

def state06 : KState := ⟨⟨362492934883176111, 362492988881284172⟩, ⟨(-471329850746412171), (-469117319111461797)⟩, true⟩

def words05 : List Nat := [371285254791163486, 371285254741017862, 371285254885686864, 371285254987870603, 371285255105025306, 371285255222970559, 371285255339408982, 371285255341473404, 371285255325836241, 371285255455868972]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484417039275947, 362484471055687209⟩, ⟨45484979714515457, 47698621718115487⟩, true⟩

def words06 : List Nat := [371285255856748443, 371285256034117194, 371285256215120798, 371285256396829959, 371285256593068732, 371285256654751665, 371285256872079185, 371285257090214471, 371285257251379832, 371285257253506859]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362504204357871032, 362504258392890174⟩, ⟨(-1155140907607543003), (-1152926136572504879)⟩, true⟩

def words07 : List Nat := [371285257400779745, 371285257562094391, 371285257851493801, 371285257853551865, 371285257851760992, 371285257803509607, 371285257931385465, 371285257974911809, 371285258289430834, 371285258604874609]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485742037148210, 362485796090734440⟩, ⟨(-34834158905786016), (-32618261124855906)⟩, true⟩

def words08 : List Nat := [371285258923669391, 371285258925724707, 371285258948560910, 371285259017257117, 371285259141927645, 371285259143987613, 371285258989073542, 371285258780282669, 371285258631412266, 371285258642659358]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471102945704395, 362471157017766124⟩, ⟨853757741371960795, 855974760525650443⟩, true⟩

def words09 : List Nat := [371285258899714437, 371285259157578534, 371285259413928622, 371285259415984287, 371285259310300807, 371285259277087007, 371285259242800278, 371285259203667033, 371285258973669428, 371285258743639694]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk606B

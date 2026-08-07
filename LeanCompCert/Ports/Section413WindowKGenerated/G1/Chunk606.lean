import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk606

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477602982991504, 362477656870132853⟩, ⟨458213814402582191, 460419618107755407⟩, true⟩

def state01 : KState := ⟨⟨362480113062240416, 362480166967680915⟩, ⟨306087215180353019, 308294127906114063⟩, true⟩

def words00 : List Nat := [371285254576736893, 371285254578789251, 371285254393232679, 371285254207588851, 371285254021191043, 371285253815110977, 371285253534194218, 371285253526583487, 371285253518251271, 371285253490167405]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498267101110572, 362498321025078689⟩, ⟨(-794315200464441720), (-792107164682552150)⟩, true⟩

def words01 : List Nat := [371285253596137812, 371285253787063865, 371285254089825749, 371285254091878645, 371285254031981462, 371285253933202650, 371285254004921886, 371285254042935674, 371285254259890631, 371285254477765340]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481780847340161, 362481834789822782⟩, ⟨205125476830370695, 207334635055763397⟩, true⟩

def words02 : List Nat := [371285254635035296, 371285254637094015, 371285254666468880, 371285254819125459, 371285255027200905, 371285255029254120, 371285254874741281, 371285254670743736, 371285254465936302, 371285254460531273]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480683551092945, 362480737512086160⟩, ⟨271764184504479896, 273974465119706262⟩, true⟩

def words03 : List Nat := [371285254621378098, 371285254839499023, 371285255057725120, 371285255084014964, 371285255174986129, 371285255266948740, 371285255630076716, 371285255632130670, 371285255632824038, 371285255560653438]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483042354498253, 362483096333901365⟩, ⟨128701100170248919, 130912497255128583⟩, true⟩

def words04 : List Nat := [371285255524308107, 371285255526594642, 371285255430419480, 371285255414178333, 371285255397324580, 371285255355332874, 371285254950213876, 371285254818347147, 371285254823071046, 371285254825199884]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk606

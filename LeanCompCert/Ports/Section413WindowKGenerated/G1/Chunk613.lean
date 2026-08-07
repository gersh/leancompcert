import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk613

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476647727942989, 362476702917210464⟩, ⟨526739541952517438, 529024711349952980⟩, true⟩

def state01 : KState := ⟨⟨362493373900582434, 362493429108444782⟩, ⟨(-498625628154322735), (-496339318797612575)⟩, true⟩

def words00 : List Nat := [371285332948430938, 371285332950726925, 371285333025557440, 371285333132510364, 371285333174525453, 371285333176641923, 371285333139509210, 371285333235074027, 371285333537563961, 371285333671756462]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 61300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 61300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493789070207222, 362493844297055905⟩, ⟨(-524080259018859037), (-521792785516453239)⟩, true⟩

def words01 : List Nat := [371285333803686337, 371285333936343218, 371285334142972429, 371285334257552815, 371285334451417794, 371285334646053515, 371285334839806518, 371285334841890827, 371285334953492355, 371285335094898138]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 61310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 61300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467730287384336, 362467785532729285⟩, ⟨1073986188009164890, 1076274795801731506⟩, true⟩

def words02 : List Nat := [371285335362766797, 371285335364845858, 371285335278415749, 371285335191968674, 371285335104758891, 371285335013832488, 371285334789302824, 371285334675071342, 371285334560114667, 371285334445101725]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 61320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 61300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510830155379320, 362510885419493526⟩, ⟨(-1569527322121196990), (-1567237563115155264)⟩, true⟩

def words03 : List Nat := [371285334160377705, 371285334142714180, 371285334369841336, 371285334461076993, 371285334506487496, 371285334552567859, 371285334837145021, 371285334990048750, 371285335407997138, 371285335826837470]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 61330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 61300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494255985903956, 362494311268815756⟩, ⟨(-552844273108751165), (-550553360965811095)⟩, true⟩

def words04 : List Nat := [371285336180350942, 371285336182430678, 371285336445190647, 371285336711347927, 371285337056530216, 371285337094555636, 371285337096128419, 371285337088937528, 371285337291527100, 371285337440174564]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 61340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 61300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485251444972593, 362485306746615265⟩, ⟨(-341115565991703), 1950945813163695⟩, true⟩

def words05 : List Nat := [371285337781076123, 371285338122827994, 371285338427687933, 371285338429767841, 371285338380488967, 371285338347488829, 371285338543733843, 371285338545827942, 371285338539832521, 371285338541690447]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497549205322356, 362497604525603341⟩, ⟨(-754913181386651000), (-752619976265588874)⟩, true⟩

def words06 : List Nat := [371285338757395918, 371285338880264620, 371285339267909445, 371285339656374131, 371285340003888399, 371285340036560965, 371285340306491421, 371285340577509231, 371285340877093280, 371285341079085188]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498958708667240, 362499014047903685⟩, ⟨(-841406314582696791), (-839111946073650983)⟩, true⟩

def words07 : List Nat := [371285341278590399, 371285341478756844, 371285341853001457, 371285342109276117, 371285342443266980, 371285342778111341, 371285343090592983, 371285343092673614, 371285343273947461, 371285343499263656]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489710795831015, 362489766153607835⟩, ⟨(-273690749815858723), (-271395243201066333)⟩, true⟩

def words08 : List Nat := [371285343988969638, 371285344174832917, 371285344296566584, 371285344418988996, 371285344620549637, 371285344722792305, 371285344923652663, 371285345125328305, 371285345313442584, 371285345387645381]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493907743133217, 362493963119726774⟩, ⟨(-531361154240090644), (-529064492369703900)⟩, true⟩

def words09 : List Nat := [371285345596662814, 371285345806770237, 371285346196203031, 371285346232692289, 371285346234302891, 371285346230727625, 371285346322334742, 371285346324651972, 371285346431823823, 371285346574517907]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk613

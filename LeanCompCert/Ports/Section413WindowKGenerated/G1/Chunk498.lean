import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk498

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486297817668715, 362486333641741870⟩, ⟨(-67765648311855615), (-66560350643204291)⟩, true⟩

def state01 : KState := ⟨⟨362484196996491961, 362484232835359600⟩, ⟨36891028360533196, 38097062872809818⟩, true⟩

def words00 : List Nat := [371284997545752149, 371284997547414684, 371284997513055800, 371284997472230987, 371284997430807869, 371284997400698495, 371284997338523992, 371284997509900608, 371284997681313358, 371284997683038236]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504034984663574, 362504070838554572⟩, ⟨(-951271882782764904), (-950065099881656372)⟩, true⟩

def words01 : List Nat := [371284998055774245, 371284998444725661, 371284999203601499, 371284999426388024, 371284999557795025, 371284999689722798, 371285000159830579, 371285000498930807, 371285000882871049, 371285001267492537]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362499080902720212, 362499116771615479⟩, ⟨(-704476562559954438), (-703269032069560792)⟩, true⟩

def words02 : List Nat := [371285001652191016, 371285001653854823, 371285001951390849, 371285002302667222, 371285002770513525, 371285002903707100, 371285002981234310, 371285003059300566, 371285003403620564, 371285003688754017]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477109635842838, 362477145519726019⟩, ⟨390573848428941198, 391782125844002472⟩, true⟩

def words03 : List Nat := [371285004375103415, 371285005062115405, 371285005680878902, 371285005763831662, 371285005970949597, 371285006178861958, 371285006592891988, 371285006594554998, 371285006472594605, 371285006316793516]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479856115427730, 362479892014189173⟩, ⟨253719506297948058, 254928525320725414⟩, true⟩

def words04 : List Nat := [371285006160214005, 371285006130652561, 371285006182455002, 371285006410498389, 371285006569198578, 371285006570861808, 371285006193467628, 371285005985070505, 371285005924708657, 371285005926432317]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487279806307834, 362487315720224609⟩, ⟨(-116361185067260533), (-115151410475792529)⟩, true⟩

def words05 : List Nat := [371285005825104836, 371285005701097141, 371285005852282365, 371285005984809737, 371285006154370119, 371285006324582313, 371285006494836175, 371285006496499813, 371285006223369900, 371285006271748330]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462075163571134, 362462111092318858⟩, ⟨1140438714929261706, 1141649229069387590⟩, true⟩

def words06 : List Nat := [371285006378689015, 371285006380352772, 371285005996791306, 371285005534964255, 371285005072502428, 371285004735274870, 371285004196232736, 371285003997058428, 371285003797319340, 371285003597413492]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362506505002100175, 362506540945902451⟩, ⟨(-1075487988028285896), (-1074276723043331008)⟩, true⟩

def words07 : List Nat := [371285003139508380, 371285003083889724, 371285003309406884, 371285003311082184, 371285003234343175, 371285003087309677, 371285003192105592, 371285003287298441, 371285003720218136, 371285004153876563]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483271325999006, 362483307284823338⟩, ⟨83529715598768645, 84741729962768867⟩, true⟩

def words08 : List Nat := [371285004580307457, 371285004678859211, 371285005133545844, 371285005589057350, 371285006056450929, 371285006058115300, 371285005990506530, 371285005889973748, 371285005854381679, 371285005856279798]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481843916280070, 362481879890090874⟩, ⟨154856038209753039, 156068800322291955⟩, true⟩

def words09 : List Nat := [371285006190369293, 371285006559150922, 371285006927976510, 371285007014444518, 371285007122236973, 371285007230927845, 371285007642608916, 371285007644274079, 371285007582182902, 371285007521359858]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk498

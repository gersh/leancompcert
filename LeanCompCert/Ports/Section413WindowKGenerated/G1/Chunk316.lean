import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk316

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362439229804014319, 362439243701012838⟩, ⟨1454932807061471014, 1455229633440133380⟩, true⟩

def state01 : KState := ⟨⟨362457530809234930, 362457544715332249⟩, ⟨876562971851908745, 876860085799150197⟩, true⟩

def words00 : List Nat := [371285293815099894, 371285293356975947, 371285292482541846, 371285291749671774, 371285291016555220, 371285290037088829, 371285287725202377, 371285286411563968, 371285285097463119, 371285284673756772]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362451148709020802, 362451162624396123⟩, ⟨1078435597502454981, 1078733004773415797⟩, true⟩

def words01 : List Nat := [371285283796976841, 371285282816280152, 371285281835222940, 371285281701410414, 371285281224355265, 371285281057474594, 371285280890247416, 371285280726024562, 371285279230398189, 371285278152693828]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362436215901160862, 362436229825600001⟩, ⟨1550732150116376086, 1551029844032727814⟩, true⟩

def words02 : List Nat := [371285277074496659, 371285276860350604, 371285275452583474, 371285274018723676, 371285272584562830, 371285271063165281, 371285269179836926, 371285268293124172, 371285267406137163, 371285266494712639]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362456228124691079, 362456242058355112⟩, ⟨917650212898246403, 917948198644767223⟩, true⟩

def words03 : List Nat := [371285264945131718, 371285264248222942, 371285263550830602, 371285263271055994, 371285261661379323, 371285259867802853, 371285258073930073, 371285256909006888, 371285255243397122, 371285254327591673]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362438826075541365, 362438840018392435⟩, ⟨1468288334807612432, 1468586611278437116⟩, true⟩

def words04 : List Nat := [371285253411433524, 371285252509979230, 371285250653897526, 371285249793525366, 371285248932704179, 371285248381545819, 371285246501535618, 371285244289204406, 371285242076583348, 371285240859191122]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362455377754345982, 362455391706358283⟩, ⟨944463989360906716, 944762555832339262⟩, true⟩

def words05 : List Nat := [371285239393868398, 371285238758758206, 371285238123360642, 371285237480256373, 371285236329643833, 371285235358354769, 371285234408364534, 371285234409390441, 371285233537114430, 371285232595677056]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469524671910992, 362469538633058533⟩, ⟨496579692829716551, 496878548569598615⟩, true⟩

def words06 : List Nat := [371285231653868436, 371285231129474544, 371285230110774241, 371285230086447253, 371285230061791906, 371285229870925834, 371285228498281597, 371285228120041982, 371285227882037126, 371285227883092307]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464990729522273, 362465004699974901⟩, ⟨640197577750947290, 640496728227374220⟩, true⟩

def words07 : List Nat := [371285227388483542, 371285226716997645, 371285226111801792, 371285226112924807, 371285225681479440, 371285225303262731, 371285224924735371, 371285224549873097, 371285223036637168, 371285222399729553]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462549041423887, 362462563020961389⟩, ⟨717657713279263718, 717957151612476004⟩, true⟩

def words08 : List Nat := [371285221787738942, 371285221788777417, 371285221177769809, 371285220483976521, 371285219789846214, 371285219404382837, 371285218627298499, 371285218735747831, 371285218736531105, 371285218658437328]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362507750973860803, 362507764962615923⟩, ⟨(-715081735924115566), (-714782005438353610)⟩, true⟩

def words09 : List Nat := [371285217944243086, 371285217521621676, 371285217426335898, 371285217427362893, 371285217057647775, 371285216523063334, 371285216200446809, 371285216201582233, 371285216633231040, 371285217345649949]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk316

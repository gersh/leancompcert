import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk706

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471667301981719, 362471741323003353⟩, ⟨953749602286518101, 957278939424892155⟩, true⟩

def state01 : KState := ⟨⟨362474882912734064, 362474956955436105⟩, ⟨726768179717532122, 730299047603389320⟩, true⟩

def words00 : List Nat := [371285300324371005, 371285300262815203, 371285300131524381, 371285300133526447, 371285300134811153, 371285300105319147, 371285299840315920, 371285299776884403, 371285299712208876, 371285299669606951]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 70600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 70600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486842776523815, 362486916841240212⟩, ⟨(-117782905984140134), (-114250483554418694)⟩, true⟩

def words01 : List Nat := [371285299524940551, 371285299381349068, 371285299278917064, 371285299281607394, 371285299225320163, 371285299207336717, 371285299188456369, 371285299170498182, 371285299017753013, 371285299043650906]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 70610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 70600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484495910631229, 362484569996906487⟩, ⟨47964196324893135, 51498141354174295⟩, true⟩

def words02 : List Nat := [371285299268393222, 371285299270812457, 371285299228714857, 371285299135860932, 371285299042050833, 371285299011803316, 371285298965100985, 371285299043612028, 371285299119961460, 371285299122509690]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 70620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 70600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489915853642383, 362489989961793527⟩, ⟨(-334899681255699529), (-331364191023235433)⟩, true⟩

def words03 : List Nat := [371285299207417059, 371285299303940013, 371285299496926633, 371285299499346335, 371285299425590383, 371285299302309084, 371285299178097214, 371285299138617975, 371285299072985806, 371285299142141721]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 70630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 70600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482994983735006, 362483069113741026⟩, ⟨154024388281864372, 157561422452131268⟩, true⟩

def words04 : List Nat := [371285299196592817, 371285299199046171, 371285299269910912, 371285299384277403, 371285299552669791, 371285299555089877, 371285299456710059, 371285299359512967, 371285299279705073, 371285299282494772]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 70640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 70600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472841147009379, 362472915298813316⟩, ⟨871447201243052856, 874985775546777590⟩, true⟩

def words05 : List Nat := [371285299304773109, 371285299359557264, 371285299374111747, 371285299376532051, 371285299124155590, 371285298911995865, 371285298698547138, 371285298685908639, 371285298513761641, 371285298341207129]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 70650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 70600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485551003524674, 362485625176983461⟩, ⟨(-26656818023975313), (-23116713478923583)⟩, true⟩

def words06 : List Nat := [371285298167606666, 371285298142706379, 371285298088967407, 371285298163919327, 371285298192348031, 371285298194768900, 371285297980926902, 371285297968295373, 371285298066601899, 371285298073737732]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 70660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 70600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474202953507287, 362474277149062864⟩, ⟨775421379127177320, 778963045362244170⟩, true⟩

def words07 : List Nat := [371285298080513416, 371285298088184469, 371285298245288362, 371285298303325447, 371285298364613819, 371285298426792262, 371285298487827708, 371285298490248731, 371285298284494956, 371285298131594871]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 70600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362471505864746318, 362471580081881431⟩, ⟨966070019227784949, 969613210812549555⟩, true⟩

def words08 : List Nat := [371285297977319337, 371285297955789077, 371285297693334499, 371285297432018962, 371285297169804551, 371285296952702711, 371285296687696659, 371285296623530803, 371285296558514141, 371285296494539694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 70680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 70600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483276087028617, 362483350326041369⟩, ⟨133992269617158455, 137537007844541889⟩, true⟩

def words09 : List Nat := [371285296302148846, 371285296288071615, 371285296339509494, 371285296341942623, 371285296219417384, 371285296066094664, 371285295911780395, 371285295862221514, 371285295711599246, 371285295686831250]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 70690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 70600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 70600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk706

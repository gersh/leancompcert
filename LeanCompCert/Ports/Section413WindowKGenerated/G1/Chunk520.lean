import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk520

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480831740521332, 362480870935793591⟩, ⟨215383843152582573, 216760764187139957⟩, true⟩

def state01 : KState := ⟨⟨362486987668181701, 362487026879056605⟩, ⟨(-104763222812095338), (-103385490360287940)⟩, true⟩

def words00 : List Nat := [371285039569960602, 371285039633105701, 371285039685931214, 371285039739418072, 371285039740766067, 371285039731826475, 371285039229748643, 371285039056725796, 371285039076985133, 371285039117037796]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477740704053558, 362477779930780149⟩, ⟨376265431415013667, 377643988394492027⟩, true⟩

def words01 : List Nat := [371285039154982743, 371285039193485313, 371285039476220095, 371285039575172295, 371285039735735326, 371285039896980512, 371285039986541055, 371285039988284198, 371285039660415625, 371285039523021489]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490245092197606, 362490284334442094⟩, ⟨(-274243655901348054), (-272864291601616414)⟩, true⟩

def words02 : List Nat := [371285039614282171, 371285039616028720, 371285039506871205, 371285039398648937, 371285039289718140, 371285039289748552, 371285039465598478, 371285039739347838, 371285039967997759, 371285040070607042]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362503497432765042, 362503536690788771⟩, ⟨(-963846277293394255), (-962466091920292389)⟩, true⟩

def words03 : List Nat := [371285040324779159, 371285040579847984, 371285041144212812, 371285041217075445, 371285041227644569, 371285041238738916, 371285041483035741, 371285041595641028, 371285041952230773, 371285042309590864]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474492124065712, 362474531397787965⟩, ⟨545683492699595624, 547064495105880022⟩, true⟩

def words04 : List Nat := [371285042599629610, 371285042601372116, 371285042516391158, 371285042635446286, 371285042768835871, 371285042770578981, 371285042470078523, 371285042168856536, 371285041866918635, 371285041762727560]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464404364382180, 362464443653813091⟩, ⟨1070922401209119160, 1072304221328842672⟩, true⟩

def words05 : List Nat := [371285041728789867, 371285041897516511, 371285042065912216, 371285042067659766, 371285041858698776, 371285041712175683, 371285041784746138, 371285041786489064, 371285041516239685, 371285041122528590]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492167553941405, 362492206858963459⟩, ⟨(-374556989769502720), (-373174357893148892)⟩, true⟩

def words06 : List Nat := [371285040728070837, 371285040669147156, 371285040425302953, 371285040371557049, 371285040317266516, 371285040218928506, 371285039814457993, 371285039779387806, 371285040074790201, 371285040214230438]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490143274136128, 362490182595099267⟩, ⟨(-269150700525423290), (-267767238520641452)⟩, true⟩

def words07 : List Nat := [371285040306152443, 371285040398672971, 371285040596562520, 371285040667541047, 371285040846478281, 371285041026058522, 371285041205297386, 371285041207049369, 371285041132843997, 371285041233786684]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468677143271914, 362468716479739608⟩, ⟨848974008381239030, 850358277945747054⟩, true⟩

def words08 : List Nat := [371285041702018131, 371285041703761922, 371285041680965136, 371285041658036355, 371285041634464413, 371285041623946077, 371285041428721705, 371285041387393422, 371285041345458763, 371285041269103128]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504330923023183, 362504370275247956⟩, ⟨(-1008412701494187713), (-1007027611064329103)⟩, true⟩

def words09 : List Nat := [371285040956902782, 371285040889894030, 371285041097362684, 371285041099137393, 371285041094330054, 371285040995781442, 371285041094828936, 371285041156184574, 371285041528369276, 371285041901299965]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk520

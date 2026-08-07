import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk635

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502624745160899, 362502684131774360⟩, ⟨(-1098962887034464751), (-1096415773917089957)⟩, true⟩

def state01 : KState := ⟨⟨362478498102059642, 362478557508150243⟩, ⟨433122530831551194, 435670880841575014⟩, true⟩

def words00 : List Nat := [371285418266340980, 371285418268498919, 371285418190675648, 371285418185832073, 371285418218597708, 371285418220755920, 371285417965522970, 371285417710198709, 371285417454024761, 371285417386607834]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476615599649277, 362476675025221602⟩, ⟨552695519833436086, 555245107226473624⟩, true⟩

def words01 : List Nat := [371285417280087320, 371285417246767781, 371285417212710135, 371285417180529030, 371285416925849663, 371285416747470614, 371285416568004636, 371285416569229155, 371285416424664323, 371285416289504135]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487569608041063, 362487629052913454⟩, ⟨(-143077809211350759), (-140526995777773951)⟩, true⟩

def words02 : List Nat := [371285416263648407, 371285416266049538, 371285416467974221, 371285416684886553, 371285416809566853, 371285416811729000, 371285416772020929, 371285416877965210, 371285417072152235, 371285417109204434]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480787012605630, 362480846477173254⟩, ⟨287925191470248530, 290477256240897314⟩, true⟩

def words03 : List Nat := [371285417145796356, 371285417183112586, 371285417467358959, 371285417629204604, 371285417832019895, 371285418035705134, 371285418237746631, 371285418239906011, 371285418111701568, 371285418042427282]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470659806151819, 362470719289950469⟩, ⟨931490107694078887, 934043394501717301⟩, true⟩

def words04 : List Nat := [371285418147782701, 371285418149942170, 371285417997303345, 371285417823656568, 371285417649157265, 371285417534458068, 371285417345283996, 371285417258344582, 371285417170715875, 371285417061697153]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490870042654917, 362490929546034358⟩, ⟨(-352990301661922769), (-350435770397572425)⟩, true⟩

def words05 : List Nat := [371285416831887191, 371285416821196848, 371285416897228912, 371285416899389740, 371285416702334806, 371285416465248361, 371285416227317361, 371285416152268631, 371285416079568383, 371285416168799929]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470521819408756, 362470581342257860⟩, ⟨940413372035040055, 942969140891940671⟩, true⟩

def words06 : List Nat := [371285416256308145, 371285416258468780, 371285416050613845, 371285416000708872, 371285415972346859, 371285415974508391, 371285415712358173, 371285415399135128, 371285415085022611, 371285414898037189]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475800571683675, 362475860113966217⟩, ⟨604886249464192980, 607443253803576690⟩, true⟩

def words07 : List Nat := [371285414666164560, 371285414653434015, 371285414639990740, 371285414626330077, 371285414453556672, 371285414356627433, 371285414406473937, 371285414408635138, 371285414260765024, 371285414112925066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479580514069561, 362479640075702762⟩, ⟨364530034083973956, 367088268838955496⟩, true⟩

def words08 : List Nat := [371285413964152802, 371285413907546120, 371285413726838784, 371285413675085949, 371285413622649034, 371285413526328942, 371285413099699942, 371285412921654671, 371285412809254793, 371285412811492021]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469132151703960, 362469191733049293⟩, ⟨1028995216243255394, 1031554704590699448⟩, true⟩

def words09 : List Nat := [371285412722340810, 371285412560399866, 371285412413049132, 371285412415453174, 371285412308444751, 371285412189871542, 371285412070587449, 371285411899861678, 371285411398958542, 371285411146643487]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk635

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk525

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478605349818200, 362478645333410188⟩, ⟨334909413791392113, 336327524958541073⟩, true⟩

def state01 : KState := ⟨⟨362455338574034003, 362455378573270545⟩, ⟨1556578639099756615, 1557997571689074773⟩, true⟩

def words00 : List Nat := [371285051691465430, 371285051693224163, 371285051451673554, 371285051103506447, 371285050754664646, 371285050518056238, 371285050099858185, 371285049764593481, 371285049428766649, 371285049065970775]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498109606689306, 362498149621851082⟩, ⟨(-689518274671793429), (-688098505769637411)⟩, true⟩

def words01 : List Nat := [371285048502130872, 371285048301436851, 371285048126672926, 371285048128476128, 371285047984783845, 371285047784007965, 371285047741986542, 371285047743924868, 371285047972748480, 371285048224205005]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473517106478755, 362473557137532939⟩, ⟨602103762844785306, 603524366496872900⟩, true⟩

def words02 : List Nat := [371285048362185108, 371285048363944508, 371285048018967691, 371285047981956627, 371285047944088111, 371285047923707800, 371285047420160702, 371285046917874304, 371285046414835175, 371285046274530786]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362460269677053344, 362460309723921467⟩, ⟨1298134799870925894, 1299556234309946210⟩, true⟩

def words03 : List Nat := [371285046161776939, 371285046268432202, 371285046374783860, 371285046376543716, 371285046000247106, 371285045646232852, 371285045291291741, 371285045264014265, 371285044799413230, 371285044330588958]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477027339844817, 362477067402499675⟩, ⟨417729150899184068, 419151414851727220⟩, true⟩

def words04 : List Nat := [371285043861015939, 371285043753984192, 371285043635919337, 371285043759079815, 371285043862072937, 371285043863842947, 371285043705985385, 371285043635429224, 371285043640729493, 371285043642553942]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486240601193928, 362486280679924853⟩, ⟨(-66441246426776132), (-65018137596556554)⟩, true⟩

def words05 : List Nat := [371285043492102044, 371285043341144722, 371285043398161668, 371285043472582771, 371285043591209302, 371285043710519751, 371285043829826408, 371285043831599206, 371285043650728575, 371285043676488911]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481802231675135, 362481842326097122⟩, ⟨166895220097148023, 168319153732986245⟩, true⟩

def words06 : List Nat := [371285044062695114, 371285044064456873, 371285044032681377, 371285043930204966, 371285043834133267, 371285043836073729, 371285043850834941, 371285044040251085, 371285044134281155, 371285044136135794]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502622524329127, 362502662634657860⟩, ⟨(-927708931011379758), (-926284161078781494)⟩, true⟩

def words07 : List Nat := [371285044376898157, 371285044679455864, 371285045249178035, 371285045381761072, 371285045459923366, 371285045538655265, 371285045657306658, 371285045659268455, 371285045969292341, 371285046306305817]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485522583327233, 362485562709530980⟩, ⟨(-28562032659659375), (-27136427935740637)⟩, true⟩

def words08 : List Nat := [371285046597622260, 371285046599384339, 371285046683286282, 371285046907418755, 371285047193511165, 371285047195273021, 371285046999761571, 371285046803945638, 371285046707751053, 371285046719571943]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473281607695876, 362473321749810195⟩, ⟨615226875242152210, 616653316782951082⟩, true⟩

def words09 : List Nat := [371285046778346852, 371285046837833554, 371285046875109041, 371285046876871218, 371285046432527484, 371285046065029112, 371285045696630613, 371285045640902681, 371285045417783408, 371285045196897324]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk525

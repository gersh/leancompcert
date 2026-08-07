import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk231

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362521630339358179, 362521637572473666⟩, ⟨(-864850444525231735), (-864737464429186949)⟩, true⟩

def state01 : KState := ⟨⟨362467362663036694, 362467369902597562⟩, ⟨389056337848531277, 389169466866648071⟩, true⟩

def words00 : List Nat := [371284207525954128, 371284207885174946, 371284207962894161, 371284208040855538, 371284208683067044, 371284208683865038, 371284208853015884, 371284209315115180, 371284209774927016, 371284209775677037]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362541668666336665, 362541675912459651⟩, ⟨(-1328568519662120325), (-1328455238960433027)⟩, true⟩

def words01 : List Nat := [371284209235056502, 371284209423456984, 371284210978371803, 371284211489193664, 371284211489755954, 371284211487458552, 371284213353707219, 371284214289143859, 371284216775000947, 371284219260975700]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362507562466870744, 362507569719550731⟩, ⟨(-539983673797819467), (-539870241464959429)⟩, true⟩

def words02 : List Nat := [371284221355803975, 371284221786537319, 371284223573966239, 371284225361606186, 371284227496095937, 371284227551912001, 371284227552457375, 371284227545509965, 371284229025181367, 371284230035081190]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362476974599406240, 362476981858609720⟩, ⟨167859504947438297, 167973088202420683⟩, true⟩

def words03 : List Nat := [371284232914282840, 371284235793522859, 371284238319909400, 371284238725529195, 371284239255494544, 371284239785772559, 371284241467489801, 371284241468216659, 371284241164086482, 371284240851185452]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362521192817711723, 362521200083421316⟩, ⟨(-855322144245571184), (-855208410406086922)⟩, true⟩

def words04 : List Nat := [371284241872469717, 371284242810173525, 371284245615617291, 371284248421124289, 371284250925085050, 371284251257236359, 371284253265931833, 371284255274828192, 371284258034703083, 371284259631155493]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362517883808041041, 362517891080372624⟩, ⟨(-778670024478514804), (-778556137305895486)⟩, true⟩

def words05 : List Nat := [371284261224450828, 371284262817861947, 371284265532852628, 371284267497638222, 371284269527199727, 371284271556866509, 371284273627107499, 371284273627834199, 371284274665939904, 371284276118267970]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362500398699804983, 362500405978624820⟩, ⟨(-373698973106072096), (-373584935632495324)⟩, true⟩

def words06 : List Nat := [371284278365429399, 371284278492049391, 371284278492602641, 371284278279951566, 371284278178509219, 371284278179327020, 371284279323014022, 371284280827697366, 371284282329364414, 371284283025984343]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501717611248510, 362501724896625065⟩, ⟨(-404226783225171196), (-404112593798584736)⟩, true⟩

def words07 : List Nat := [371284284376686142, 371284285727636397, 371284288942048910, 371284289675806225, 371284290079995662, 371284290484376086, 371284290940473515, 371284290941274409, 371284291220499077, 371284291973377639]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470817645923123, 362470824937866701⟩, ⟨312055634166663410, 312169975849097832⟩, true⟩

def words08 : List Nat := [371284292723478088, 371284292724205707, 371284291445930529, 371284291549289723, 371284292211780935, 371284292212508528, 371284290397305618, 371284288425299699, 371284286453167918, 371284286342603618]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362440012186674844, 362440019485186126⟩, ⟨1026665404958037101, 1026779898978893357⟩, true⟩

def words09 : List Nat := [371284285932540575, 371284286103217272, 371284286268129616, 371284286268857543, 371284283957664353, 371284282207335962, 371284280565394898, 371284280566135507, 371284279146367531, 371284277239452458]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk231

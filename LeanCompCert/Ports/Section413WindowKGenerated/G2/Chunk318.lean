import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk318

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614204500669302, 360614210613091895⟩, ⟨(-1010646940515274292), (-1010515500643431208)⟩, true⟩

def state01 : KState := ⟨⟨360557321593902328, 360557327710316332⟩, ⟨798306223502616854, 798437790321227832⟩, true⟩

def words00 : List Nat := [360582434761910009, 360582434762333344, 360582434141647049, 360582433027725400, 360582431913804829, 360582430553340282, 360582429807990367, 360582429389772714, 360582428971528439, 360582427923781319]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 31800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 31800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589914748607662, 360589920869016611⟩, ⟨(-238800636359811153), (-238668942442095939)⟩, true⟩

def words01 : List Nat := [360582427135083528, 360582426640611496, 360582426182988324, 360582426183411838, 360582425234221506, 360582423318064136, 360582421401946109, 360582420469785891, 360582420273278102, 360582420509428852]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 31810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 31800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360538146347433967, 360538152471882095⟩, ⟨1408610884741175772, 1408742707205647152⟩, true⟩

def words02 : List Nat := [360582420509806259, 360582420253248908, 360582420031172460, 360582419893919268, 360582419756556252, 360582419084935176, 360582417427598301, 360582415227943229, 360582413028351274, 360582410803870963]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 31820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 31800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360482005455700430, 360482011584136982⟩, ⟨3196075870416906538, 3196207819853027602⟩, true⟩

def words03 : List Nat := [360582409413797644, 360582408762298636, 360582408110797650, 360582406923671042, 360582405607478588, 360582404046016869, 360582402484523266, 360582400808745695, 360582398147970395, 360582394995564527]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 31830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 31800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360539847278006739, 360539853410450736⟩, ⟨1353921694487346955, 1354053771539836381⟩, true⟩

def words04 : List Nat := [360582391843261898, 360582389018899080, 360582386871188553, 360582384699126171, 360582382527168857, 360582379398410058, 360582375285080940, 360582372153643707, 360582369022279185, 360582366872665488]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 31840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 31800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360535576116702215, 360535582253184763⟩, ⟨1489936784079749281, 1490068989779984079⟩, true⟩

def words05 : List Nat := [360582365538286021, 360582363705906254, 360582361873560656, 360582360693962049, 360582360012972547, 360582358796548719, 360582357580159172, 360582355440860964, 360582352992198074, 360582351524678172]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360522566634382351, 360522572774857810⟩, ⟨1904464015430831923, 1904596348365456963⟩, true⟩

def words06 : List Nat := [360582350057105300, 360582349330744867, 360582347932155499, 360582345831264449, 360582343730428924, 360582341385151840, 360582339595479724, 360582337959807775, 360582336324195449, 360582334191499337]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360555093618868853, 360555099763357565⟩, ⟨867427456655534180, 867559917511362856⟩, true⟩

def words07 : List Nat := [360582332316745551, 360582330071142912, 360582327825557095, 360582326560080508, 360582324311915254, 360582321115778876, 360582317919760030, 360582315452250040, 360582313913848848, 360582313060644622]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360512843159873277, 360512849308400219⟩, ⟨2214514138332923731, 2214646727948159489⟩, true⟩

def words08 : List Nat := [360582312207433008, 360582310864207225, 360582309115596159, 360582308346385306, 360582307577116690, 360582306121892395, 360582303997156204, 360582301372613055, 360582298748157353, 360582295740759836]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360486270012567769, 360486276165098816⟩, ⟨3062241796811480445, 3062374514137382131⟩, true⟩

def words09 : List Nat := [360582293563484792, 360582292365269960, 360582291167075557, 360582289479276300, 360582287266680317, 360582284810137398, 360582282353620099, 360582280636834570, 360582278375199450, 360582275366168954]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk318

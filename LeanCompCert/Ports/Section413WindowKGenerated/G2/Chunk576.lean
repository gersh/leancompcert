import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk576

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579157010302277, 360579178064108104⟩, ⟨158123068228297037, 158942381458643889⟩, true⟩

def state01 : KState := ⟨⟨360573668371398977, 360573689432781208⟩, ⟨474270467791946727, 475090217461620293⟩, true⟩

def words00 : List Nat := [360581937686688960, 360581937724261835, 360581937724993633, 360581937514571734, 360581937304026357, 360581936954528087, 360581936755419280, 360581936601703555, 360581936447910831, 360581936095122150]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 57600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 57600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585166307461788, 360585187376429907⟩, ⟨(-188238699601568830), (-187418512871862232)⟩, true⟩

def words01 : List Nat := [360581936016415018, 360581936081085155, 360581936245054365, 360581936245858187, 360581936109375945, 360581935686867725, 360581935264227756, 360581934833246427, 360581934711368424, 360581934768650246]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 57610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 57600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360549472026204883, 360549493102829278⟩, ⟨1868583456028236678, 1869404083949730298⟩, true⟩

def words02 : List Nat := [360581934769366514, 360581934674697359, 360581934383251830, 360581934251484758, 360581934119494510, 360581933905736083, 360581933391493814, 360581932687030309, 360581931982445326, 360581931140031252]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 57620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 57600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360533383751153466, 360533404835354800⟩, ⟨2795775456612518559, 2796596521231866669⟩, true⟩

def words03 : List Nat := [360581930577835189, 360581930007307805, 360581929436712506, 360581928714435364, 360581927691715060, 360581926592658593, 360581925493396202, 360581924695274453, 360581924005932570, 360581923165008372]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 57630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 57600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586970447844681, 360586991539631842⟩, ⟨(-293210926721200879), (-292389424818008583)⟩, true⟩

def words04 : List Nat := [360581922323925589, 360581921784006291, 360581921435321277, 360581921286704803, 360581921138051478, 360581920699790317, 360581920309014231, 360581920018144059, 360581919736112947, 360581919824920597]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 57640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 57600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360568963271897616, 360568984371351444⟩, ⟨745040474082363599, 745862418007603713⟩, true⟩

def words05 : List Nat := [360581919825641936, 360581919688513300, 360581919714059311, 360581920030813589, 360581920182725000, 360581920334759261, 360581920335475869, 360581920335860044, 360581920120585317, 360581919897158028]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 57650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 57600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581736225720561, 360581757332751184⟩, ⟨8437330398161241, 9259711239009597⟩, true⟩

def words06 : List Nat := [360581919673471848, 360581919559327720, 360581919401692965, 360581919052437584, 360581918703062141, 360581918208708601, 360581917987862235, 360581918028245661, 360581918028962633, 360581917896497309]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 57660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 57600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591880903175960, 360591902017806423⟩, ⟨(-576765893493787786), (-575943074332570592)⟩, true⟩

def words07 : List Nat := [360581918110657138, 360581918327838815, 360581918374914916, 360581918375719556, 360581918122887201, 360581917613520119, 360581917104016616, 360581916827142079, 360581916873506717, 360581917047463805]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 57670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 57600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566932347922028, 360566953470223413⟩, ⟨862224108885947632, 863047370541824510⟩, true⟩

def words08 : List Nat := [360581917048193335, 360581916980314305, 360581916691217029, 360581916575694378, 360581916459953465, 360581916229220244, 360581915698577177, 360581914884358053, 360581914070013013, 360581913556382918]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 57680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 57600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567460187516974, 360567481317395994⟩, ⟨831819028859042097, 832642727707371149⟩, true⟩

def words09 : List Nat := [360581913297720079, 360581913218569154, 360581913139333180, 360581912908781315, 360581912805737292, 360581912508488040, 360581912213225606, 360581912214032774, 360581912116535969, 360581911867269606]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 57690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 57600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 57600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk576

import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk995

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487782421520037, 362487933393700040⟩, ⟨(-266115387118716631), (-255973615596317999)⟩, true⟩

def state01 : KState := ⟨⟨362483717175078999, 362483868178814996⟩, ⟨138365193729022018, 148510105233104710⟩, true⟩

def words00 : List Nat := [371285360836149181, 371285360839665611, 371285360785793389, 371285360799093082, 371285360816690029, 371285360820212025, 371285360747362106, 371285360665479381, 371285360588700420, 371285360592695341]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473738425690863, 362473889460990527⟩, ⟨1131450858344094256, 1141598910911714504⟩, true⟩

def words01 : List Nat := [371285360658918205, 371285360741659911, 371285360823067346, 371285360826565926, 371285360773209995, 371285360740587751, 371285360713020002, 371285360716528350, 371285360622422075, 371285360511140364]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491895819697473, 362492046886327028⟩, ⟨(-675654157939650383), (-665502987268359263)⟩, true⟩

def words02 : List Nat := [371285360398253390, 371285360359244332, 371285360300879160, 371285360324772345, 371285360331061471, 371285360334621577, 371285360277431726, 371285360302416519, 371285360426485577, 371285360497289760]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483769503286376, 362483920601817680⟩, ⟨133213527363030822, 143367873373735262⟩, true⟩

def words03 : List Nat := [371285360567040424, 371285360637916253, 371285360735821782, 371285360789782468, 371285360851485819, 371285360914568756, 371285360976320573, 371285360979820147, 371285360916006826, 371285360905950428]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474561468383769, 362474712598050546⟩, ⟨1049819878257994361, 1059977323654856633⟩, true⟩

def words04 : List Nat := [371285360922030144, 371285360925530182, 371285360835427103, 371285360746449916, 371285360656097234, 371285360591789530, 371285360483483795, 371285360418188381, 371285360351768915, 371285360285882338]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498940368854858, 362499091530189525⟩, ⟨(-1377211736181801043), (-1367051138090045865)⟩, true⟩

def words05 : List Nat := [371285360181298081, 371285360179536001, 371285360263765489, 371285360295796315, 371285360311301997, 371285360327866257, 371285360417573358, 371285360458463465, 371285360598754026, 371285360740642514]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485426630463527, 362485577823407239⟩, ⟨(-31745175021304635), (-21581429770150839)⟩, true⟩

def words06 : List Nat := [371285360846553804, 371285360850054617, 371285360919550625, 371285361007720172, 371285361124609397, 371285361128109800, 371285361110744144, 371285361078747964, 371285361073106359, 371285361079277220]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478644115624158, 362478795340038724⟩, ⟨643668438060260153, 653835317025622261⟩, true⟩

def words07 : List Nat := [371285361184723299, 371285361291590532, 371285361397192411, 371285361400693134, 371285361371748773, 371285361346083292, 371285361389480142, 371285361392980902, 371285361332132802, 371285361270115302]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485884951893921, 362486036207672215⟩, ⟨(-77365647716857146), (-67195645392834156)⟩, true⟩

def words08 : List Nat := [371285361241495946, 371285361245421838, 371285361294732862, 371285361347184020, 371285361381922187, 371285361385436279, 371285361377924477, 371285361420467889, 371285361481224405, 371285361491629673]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488601591894993, 362488752879617402⟩, ⟨(-347932869390157879), (-337759685594871527)⟩, true⟩

def words09 : List Nat := [371285361496597405, 371285361502780536, 371285361557437035, 371285361578626616, 371285361628777594, 371285361680304094, 371285361730528938, 371285361734038268, 371285361713721395, 371285361752162910]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk995

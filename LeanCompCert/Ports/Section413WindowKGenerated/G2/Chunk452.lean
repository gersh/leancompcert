import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk452

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607396506127230, 360607409217082992⟩, ⟨(-1093821722870703249), (-1093433470856602549)⟩, true⟩

def state01 : KState := ⟨⟨360604615682890912, 360604628399737534⟩, ⟨(-968359959921761274), (-967971441611476544)⟩, true⟩

def words00 : List Nat := [360583218918838871, 360583218919457670, 360583218768922616, 360583218774566225, 360583218775084188, 360583218656363969, 360583218553747470, 360583218205759481, 360583217857668661, 360583218312776143]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593538113853993, 360593550836536941⟩, ⟨(-467429224856231791), (-467040442657057447)⟩, true⟩

def words01 : List Nat := [360583219049333763, 360583219785976888, 360583220146347572, 360583220598644286, 360583220926691689, 360583221254894731, 360583221949037371, 360583222423763418, 360583222652718541, 360583222881766878]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586834432271380, 360586847160792403⟩, ⟨(-164218292060609592), (-163829245834532032)⟩, true⟩

def words02 : List Nat := [360583223185861315, 360583223736112631, 360583224575154719, 360583225414277988, 360583225817105016, 360583225817724117, 360583225733080860, 360583225400293235, 360583225067339374, 360583225104109276]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579451043944143, 360579463778362946⟩, ⟨169844199004348752, 170233512015748612⟩, true⟩

def words03 : List Nat := [360583225104660862, 360583224939921446, 360583225097701523, 360583225803632305, 360583226333305766, 360583226863056949, 360583227054303935, 360583227054923197, 360583226758974789, 360583226676506531]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556124998505155, 360556137738758818⟩, ⟨1225059269313684286, 1225448846324263388⟩, true⟩

def words04 : List Nat := [360583226593842211, 360583226349940684, 360583225618898538, 360583224516148273, 360583223413345841, 360583222186865432, 360583221205845112, 360583220712712426, 360583220219523304, 360583219481219023]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360608543713508481, 360608556459609676⟩, ⟨(-1147253282292890772), (-1146863440653136986)⟩, true⟩

def words05 : List Nat := [360583218883241874, 360583218563344811, 360583218243275999, 360583217961178915, 360583217820124929, 360583217212889588, 360583216605562622, 360583216450056282, 360583217010433783, 360583217570927298]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601214833928524, 360601227585942405⟩, ⟨(-815528852536034563), (-815138743259432935)⟩, true⟩

def words06 : List Nat := [360583217842036868, 360583218264036159, 360583219173230495, 360583220082567429, 360583220668383310, 360583221112274417, 360583221278246075, 360583221444277949, 360583221444788225, 360583221826333397]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360542465170279741, 360542477928131074⟩, ⟨1844453005633413217, 1844843379200246113⟩, true⟩

def words07 : List Nat := [360583222385232043, 360583222944223249, 360583223258239150, 360583223258858942, 360583223086385909, 360583222788524931, 360583222490480096, 360583222405868410, 360583221834802017, 360583220935622246]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565935870241354, 360565948633949137⟩, ⟨781571831448765925, 781962470225238807⟩, true⟩

def words08 : List Nat := [360583220036341969, 360583219624253814, 360583219457182534, 360583219278081040, 360583219098939227, 360583218506312405, 360583217427358949, 360583216225998429, 360583215024500913, 360583214310041547]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586834977697362, 360586847747307471⟩, ⟨(-165096821599666074), (-164705915478014322)⟩, true⟩

def words09 : List Nat := [360583213929377891, 360583213279831192, 360583212630191568, 360583212549195224, 360583212549714256, 360583212508219256, 360583212466671915, 360583212047608069, 360583211854425755, 360583211935394313]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk452

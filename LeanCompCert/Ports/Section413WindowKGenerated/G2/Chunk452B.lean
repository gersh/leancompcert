import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk452A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk452B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk452A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk452B

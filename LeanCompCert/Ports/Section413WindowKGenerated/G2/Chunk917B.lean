import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk917A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk917B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk917A

def state06 : KState := ⟨⟨360581699303523325, 360581754732308280⟩, ⟨16420236526076592, 19854761240855248⟩, true⟩

def words05 : List Nat := [360581972820636101, 360581972551305041, 360581972281590265, 360581972130771316, 360581971945327721, 360581971658314293, 360581971371028513, 360581971202760900, 360581971110375524, 360581971109392422]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583413067333600, 360583468508775323⟩, ⟨(-140927852864758641), (-137492166705761407)⟩, true⟩

def words06 : List Nat := [360581971108216285, 360581971040951499, 360581971003177041, 360581970963150259, 360581970922758826, 360581970852897027, 360581970743018416, 360581970558617877, 360581970373967117, 360581970299464040]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557482585144896, 360557538039068360⟩, ⟨2238904467257756663, 2242341298929119883⟩, true⟩

def words07 : List Nat := [360581970435442042, 360581970571671492, 360581970612570760, 360581970613897459, 360581970536200373, 360581970428327386, 360581970320085983, 360581970207977724, 360581970002505180, 360581969737683844]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575473761891155, 360575529228332377⟩, ⟨587600453621366508, 591038434235460392⟩, true⟩

def words08 : List Nat := [360581969472560574, 360581969326401819, 360581969239631458, 360581969193180163, 360581969146595529, 360581968994747881, 360581968724175521, 360581968551142533, 360581968377725811, 360581968256921935]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565713528577658, 360565769007690186⟩, ⟨1483489826030348891, 1486928969802062009⟩, true⟩

def words09 : List Nat := [360581968187988426, 360581968027823391, 360581967867414153, 360581967690162126, 360581967571978457, 360581967377695274, 360581967183271818, 360581966911734213, 360581966665930844, 360581966491021364]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk917B

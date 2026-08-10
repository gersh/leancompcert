import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk628A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk628B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk628A

def state06 : KState := ⟨⟨360560647803778131, 360560673053297858⟩, ⟨1380589379820771992, 1381661573410029576⟩, true⟩

def words05 : List Nat := [360582653981841185, 360582654160565807, 360582654161366175, 360582654118399272, 360582654035957841, 360582653813220526, 360582653590221356, 360582653569271616, 360582653382526373, 360582653033784814]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360596123284764836, 360596148542612850⟩, ⟨(-849552384326362586), (-848479667180026952)⟩, true⟩

def words06 : List Nat := [360582652684838501, 360582652618208239, 360582652795913347, 360582652973781529, 360582652974608727, 360582652904682654, 360582652813219619, 360582652712336112, 360582652762039745, 360582652977611816]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603361316051882, 360603386582303649⟩, ⟨(-1304637406254458934), (-1303564160722239224)⟩, true⟩

def words07 : List Nat := [360582653042226147, 360582653106933909, 360582653424154764, 360582653935863774, 360582654379277292, 360582654822825781, 360582655139081794, 360582655268686576, 360582655599096904, 360582655929789818]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586619729945619, 360586645004523853⟩, ⟨(-251936998663611865), (-250863229521551315)⟩, true⟩

def words08 : List Nat := [360582656156633805, 360582656268744883, 360582656269541784, 360582656199673521, 360582656129663371, 360582656019807644, 360582656083088929, 360582656146547887, 360582656147334621, 360582656147143282]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360635911686929806, 360635936969845199⟩, ⟨(-3352188632895366094), (-3351114339388859210)⟩, true⟩

def words09 : List Nat := [360582656389448591, 360582656632014204, 360582657075899145, 360582657568760221, 360582657817464924, 360582658066216462, 360582658567243352, 360582659263647888, 360582660111384919, 360582660959298644]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk628B

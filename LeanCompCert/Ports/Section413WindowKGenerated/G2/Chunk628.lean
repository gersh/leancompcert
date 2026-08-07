import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk628

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360537191934348495, 360537217133765954⟩, ⟨2852968293927862334, 2854037339593851146⟩, true⟩

def state01 : KState := ⟨⟨360578343506649694, 360578368714387824⟩, ⟨268421334374157998, 269490902619979392⟩, true⟩

def words00 : List Nat := [360582662865272825, 360582662395910747, 360582662054349319, 360582661787722783, 360582661521021004, 360582661032162654, 360582660394075118, 360582659959949015, 360582659525578093, 360582659287586678]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583366445267427, 360583391661421740⟩, ⟨(-47169080256311430), (-46098983349295642)⟩, true⟩

def words01 : List Nat := [360582659220084182, 360582658954331042, 360582658688418069, 360582658566234788, 360582658566974908, 360582658441447293, 360582658315823182, 360582658062914801, 360582657833864803, 360582657846561275]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577301067761119, 360577326292214894⟩, ⟨333807206134886822, 334877824455598064⟩, true⟩

def words02 : List Nat := [360582657897836145, 360582657898718323, 360582657771127356, 360582657495802516, 360582657220356265, 360582656766378322, 360582656473901073, 360582656434663004, 360582656395341617, 360582656195516750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583677861034997, 360583703093829397⟩, ⟨(-66856046078259000), (-65784903675401498)⟩, true⟩

def words03 : List Nat := [360582656220579326, 360582656330752535, 360582656549788323, 360582656586684976, 360582656587498768, 360582656385871120, 360582656184080177, 360582656212009252, 360582656229394771, 360582656246967072]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577914970721250, 360577940211915316⟩, ⟨295182260696326678, 296253930976615438⟩, true⟩

def words04 : List Nat := [360582656247753163, 360582656138021279, 360582655953038715, 360582655717052615, 360582655480840254, 360582655180881513, 360582654928189241, 360582654549690583, 360582654171036889, 360582653878279304]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk628

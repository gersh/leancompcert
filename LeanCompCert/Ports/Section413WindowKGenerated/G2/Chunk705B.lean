import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk705A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk705B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk705A

def state06 : KState := ⟨⟨360567800022405569, 360567832131129669⟩, ⟨1030414908074234110, 1031945226061417358⟩, true⟩

def words05 : List Nat := [360582457938904534, 360582457881390359, 360582457823700566, 360582457849752095, 360582457852860434, 360582457856132385, 360582457857024060, 360582457734534938, 360582457411298250, 360582457205195166]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360542757797097085, 360542789915233723⟩, ⟨2797507828917422850, 2799038811101211618⟩, true⟩

def words06 : List Nat := [360582456998735416, 360582456912653506, 360582456625916798, 360582456216049272, 360582455806029693, 360582455264518581, 360582454844091930, 360582454333439057, 360582453822700110, 360582453211409169]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579242664947482, 360579274792521042⟩, ⟨222609577879389071, 224141226074259645⟩, true⟩

def words07 : List Nat := [360582452650183820, 360582452289630261, 360582451928793537, 360582451768532832, 360582451642755349, 360582451344695444, 360582451046449912, 360582450743237282, 360582450541015781, 360582450497055957]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568529776672468, 360568561913787202⟩, ⟨978634493701448948, 980166815358766048⟩, true⟩

def words08 : List Nat := [360582450452968917, 360582450253221418, 360582449852843061, 360582449653081425, 360582449453059320, 360582449158486184, 360582448758110785, 360582448193057653, 360582447627811693, 360582447263204383]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553444942446592, 360553477088972266⟩, ⟨2043583313584028689, 2045116299607303313⟩, true⟩

def words09 : List Nat := [360582447067311848, 360582447019741055, 360582446972062708, 360582446824110869, 360582446542594041, 360582446122788460, 360582445702690145, 360582445441497611, 360582445151216944, 360582444741941208]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk705B

import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk362A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk362B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk362A

def state06 : KState := ⟨⟨360585479575635051, 360585487609642312⟩, ⟨(-127625664376286429), (-127428732333003171)⟩, true⟩

def words05 : List Nat := [360581976281754461, 360581976651372642, 360581976999090667, 360581976999578111, 360581976588754489, 360581975535269744, 360581974481748427, 360581973652759291, 360581973303217759, 360581973400648269]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360554601311449262, 360554609350101442⟩, ⟨991923815935626088, 992120916426173742⟩, true⟩

def words06 : List Nat := [360581973401088150, 360581972947939794, 360581971736466020, 360581971284270691, 360581970831971382, 360581970187256499, 360581968784360625, 360581966640273989, 360581964496212305, 360581963111238089]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360553249807129801, 360553257850372689⟩, ⟨1040889354819750071, 1041086621838498597⟩, true⟩

def words07 : List Nat := [360581962357484290, 360581961534806865, 360581960712121606, 360581959485671840, 360581958286226543, 360581956882655484, 360581955479019104, 360581954834133595, 360581954523476296, 360581953733003299]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360551499189288542, 360551507237142926⟩, ⟨1104336661612612158, 1104534095959380754⟩, true⟩

def words08 : List Nat := [360581952942470543, 360581951931591960, 360581951302758958, 360581950898489032, 360581950494203378, 360581949343606758, 360581947435622565, 360581946107232374, 360581944778760480, 360581943558332218]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360539334751151285, 360539342803651827⟩, ⟨1545870141377519831, 1546067744355879007⟩, true⟩

def words09 : List Nat := [360581942720092891, 360581941499168451, 360581940278217753, 360581939845650867, 360581939846067585, 360581939162304136, 360581938478527050, 360581937304989276, 360581935374356340, 360581934201567967]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk362B

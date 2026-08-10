import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk892A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk892B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk892A

def state06 : KState := ⟨⟨360565142179887102, 360565194517087653⟩, ⟨1502482581221856861, 1505637267454842927⟩, true⟩

def words05 : List Nat := [360582062945643486, 360582063022893966, 360582063025492911, 360582063026788595, 360582063010060501, 360582062962063817, 360582062913708672, 360582062825013446, 360582062700111508, 360582062512465817]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581810668891383, 360581863018239765⟩, ⟨14592835363405167, 17748605969684531⟩, true⟩

def words06 : List Nat := [360582062324532265, 360582062283580953, 360582062365133365, 360582062446951658, 360582062448146828, 360582062403834627, 360582062233951830, 360582062060223948, 360582061886121172, 360582061837618837]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590261459426307, 360590313821060525⟩, ⟨(-739883487816418437), (-736726620392396931)⟩, true⟩

def words07 : List Nat := [360582061836575215, 360582061737409451, 360582061662846377, 360582061752060273, 360582061808843668, 360582061865843387, 360582061866990305, 360582061861099470, 360582061953309070, 360582062047218472]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571664732363298, 360571717106116552⟩, ⟨920477570319773593, 923635519793152483⟩, true⟩

def words08 : List Nat := [360582062140626690, 360582062141914058, 360582062110134723, 360582062015619887, 360582061920906136, 360582061740346564, 360582061638530318, 360582061556306580, 360582061473956175, 360582061327415613]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580823417924487, 360580875803851700⟩, ⟨102653137197238290, 105812173742109872⟩, true⟩

def words09 : List Nat := [360582061212608783, 360582061166432705, 360582061197471794, 360582061198759323, 360582061152301862, 360582060999678574, 360582060846816873, 360582060731893759, 360582060722543671, 360582060710612530]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk892B

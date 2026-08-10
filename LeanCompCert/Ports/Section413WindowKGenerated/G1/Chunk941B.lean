import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk941A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk941B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk941A

def state06 : KState := ⟨⟨362496871721126585, 362497006351067695⟩, ⟨(-1123626859080874664), (-1115067935523274908)⟩, true⟩

def words05 : List Nat := [371285163247710699, 371285163356770249, 371285163576951914, 371285163658703694, 371285163722177576, 371285163786647889, 371285163896620166, 371285163951483015, 371285164079498123, 371285164209039432]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487786170330207, 362487920829980511⟩, ⟨(-268130414739894555), (-259568693615891325)⟩, true⟩

def words06 : List Nat := [371285164336981507, 371285164352339958, 371285164413479070, 371285164476361769, 371285164558466281, 371285164561764088, 371285164503729362, 371285164447230179, 371285164442084925, 371285164475119504]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478562642685257, 362478697332056192⟩, ⟨600490065452510159, 609054585516016361⟩, true⟩

def words07 : List Nat := [371285164520061336, 371285164566278219, 371285164611097206, 371285164614395377, 371285164508773144, 371285164439297277, 371285164380232817, 371285164383592207, 371285164317673808, 371285164252692379]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486940246250625, 362487074965106119⟩, ⟨(-188524956205937529), (-179957659136087227)⟩, true⟩

def words08 : List Nat := [371285164214550575, 371285164218210445, 371285164278871362, 371285164352932855, 371285164401560344, 371285164404858871, 371285164302835106, 371285164296363472, 371285164380322176, 371285164404021344]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483165601461153, 362483300350443667⟩, ⟨167045681248383377, 175615816133590921⟩, true⟩

def words09 : List Nat := [371285164426507509, 371285164450218304, 371285164529724981, 371285164554200082, 371285164611511686, 371285164670057087, 371285164713860057, 371285164717174822, 371285164652907013, 371285164637239141]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk941B

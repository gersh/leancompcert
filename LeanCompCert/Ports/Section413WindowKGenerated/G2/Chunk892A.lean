import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk892A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568324887446611, 360568377151596936⟩, ⟨1217188604804910328, 1220336772770087396⟩, true⟩

def state01 : KState := ⟨⟨360601218154021193, 360601270430333413⟩, ⟨(-1717113491447683530), (-1713964238582435118)⟩, true⟩

def words00 : List Nat := [360582057904807271, 360582057749994660, 360582057690158562, 360582057723749773, 360582057724938578, 360582057653858685, 360582057595056465, 360582057603584021, 360582057737157959, 360582057953860978]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593136428417936, 360593188716964374⟩, ⟨(-996081080763086123), (-992930736420438895)⟩, true⟩

def words01 : List Nat := [360582058095806191, 360582058237888538, 360582058505179104, 360582058835861269, 360582059079823681, 360582059323975959, 360582059486082097, 360582059574510559, 360582059700293512, 360582059826496655]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595185784278004, 360595238084950090⟩, ⟨(-1178946667071501649), (-1175795240816151917)⟩, true⟩

def words02 : List Nat := [360582059971589536, 360582060119770213, 360582060204805906, 360582060289982841, 360582060316579999, 360582060406822901, 360582060622088623, 360582060837596230, 360582060954392438, 360582061103398655]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611696491995209, 360611748804811835⟩, ⟨(-2652326722177769015), (-2649174212206024591)⟩, true⟩

def words03 : List Nat := [360582061377517339, 360582061652024442, 360582061917232951, 360582062057271211, 360582062092781340, 360582062128400854, 360582062289146780, 360582062519397889, 360582062853094531, 360582063187077767]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580072041823005, 360580124366916142⟩, ⟨169859611623836865, 173013217207325863⟩, true⟩

def words04 : List Nat := [360582063453365643, 360582063594393369, 360582063635785136, 360582063677540644, 360582063678622566, 360582063650821128, 360582063497491198, 360582063269472098, 360582063041212201, 360582062890358241]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk892A

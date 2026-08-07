import LeanCompCert.Ports.Section413G1Full99999Certificate
import LeanCompCert.Ports.Section413G2Full99999Certificate
import LeanCompCert.Ports.Section413WindowKGenerated.G1.Aggregate
import LeanCompCert.Ports.Section413WindowKGenerated.G2.Aggregate
import LeanCompCert.Ports.Section413WindowTraceLemmas
import LeanCompCert.Ports.TotalWordBounds

/-!
# Verified-code certificate for the Section 4.1.3 fixed window

The two source tables are established by their complete compiled arithmetic
sweeps.  Generated, bounded kernel shards connect the paper's exact `kStep`
recurrence to 199,998 nonnegative event words.  A uniform LeanCompCert loop
then checks every word against the common bound.  The only atom in this file
is that physical compiled-loop result; it is no longer a constant Boolean
carrier.
-/

namespace LeanCompCert.Ports.Section413Window99999Certificate

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowTableApplications
open LeanCompCert.Ports.Section413WindowDirectTables

def g1Words : List Nat :=
  LeanCompCert.Ports.Section413WindowKGenerated.G1.allWords

def g2Words : List Nat :=
  LeanCompCert.Ports.Section413WindowKGenerated.G2.allWords

def windowWords : List Nat := g1Words ++ g2Words

def windowComputation : LeanCompCert.Verified.Computation :=
  LeanCompCert.Ports.TotalWordBounds.boundsComputation
    "section413-window-99999" commonBound windowWords

/-- Physical CompCert result for all 199,998 event-bound comparisons. -/
axiom section413Window99999_compcert_run :
  windowComputation.Returns ((0 : Nat) : Int)

private theorem g1Words_length : g1Words.length = 99999 := by
  have h :=
    LeanCompCert.Ports.Section413WindowTraceLemmas.trace_words_length
      directG1 1 40 36393 8800000000000000 0 99999 initialKState
  rw [LeanCompCert.Ports.Section413WindowKGenerated.G1.fullTrace] at h
  simpa [g1Words] using h

private theorem g2Words_length : g2Words.length = 99999 := by
  have h :=
    LeanCompCert.Ports.Section413WindowTraceLemmas.trace_words_length
      directG2 2 16 37273 0 0 99999 initialKState
  rw [LeanCompCert.Ports.Section413WindowKGenerated.G2.fullTrace] at h
  simpa [g2Words] using h

private theorem all_window_words_le :
    ∀ word ∈ windowWords, word ≤ commonBound := by
  apply LeanCompCert.Ports.TotalWordBounds.all_le_of_returns_zero
    "section413-window-99999" commonBound windowWords
  · decide
  · simp [windowWords, g1Words_length, g2Words_length]
    decide
  · exact section413Window99999_compcert_run

private theorem g1_trace_ok :
    (trace directG1 1 40 36393 8800000000000000 0 99999
      initialKState).1.ok = true := by
  apply trace_safe directG1 1 40 36393 8800000000000000 0 99999
    initialKState
  · decide
  · decide
  · rfl
  · intro word hword
    apply all_window_words_le word
    simp only [windowWords, List.mem_append, g1Words, g2Words]
    left
    rw [LeanCompCert.Ports.Section413WindowKGenerated.G1.fullTrace] at hword
    exact hword

private theorem g2_trace_ok :
    (trace directG2 2 16 37273 0 0 99999 initialKState).1.ok = true := by
  apply trace_safe directG2 2 16 37273 0 0 99999 initialKState
  · decide
  · decide
  · rfl
  · intro word hword
    apply all_window_words_le word
    simp only [windowWords, List.mem_append, g1Words, g2Words]
    right
    rw [LeanCompCert.Ports.Section413WindowKGenerated.G2.fullTrace] at hword
    exact hword

private theorem g1_run_ok :
    (kRun directG1 1 40 36393 100000 99999).ok = true := by
  rw [kRun_eq_segment]
  change
    (kSegment directG1 1 40 36393 100000 0 99999 initialKState).ok = true
  rw [← trace_fst_eq_segment directG1 1 40 36393 8800000000000000
    0 99999 initialKState]
  exact g1_trace_ok

private theorem g2_run_ok :
    (kRun directG2 2 16 37273 100000 99999).ok = true := by
  rw [kRun_eq_segment]
  change
    (kSegment directG2 2 16 37273 100000 0 99999 initialKState).ok = true
  rw [← trace_fst_eq_segment directG2 2 16 37273 0
    0 99999 initialKState]
  exact g2_trace_ok

private def g1Table : Array Cell :=
  LeanCompCert.Ports.Section413G1Generated99999Chunks.expected99999

private def g2Table : Array Cell :=
  LeanCompCert.Ports.Section413G2Generated99999Chunks.expected99999

private theorem window_table_ok :
    windowTableOK g1Table g2Table 99999 = true := by
  unfold windowTableOK
  simp only [g1Table, g2Table]
  rw [LeanCompCert.Ports.Section413WindowDirectTables.expectedG1_eq_direct,
    LeanCompCert.Ports.Section413WindowDirectTables.expectedG2_eq_direct,
    g1_run_ok, g2_run_ok]
  rfl

theorem windowOK_999_99999 : windowOK 999 99999 = true := by
  apply windowOK_of_tables 999 33 99999 g1Table g2Table
  · simp [g1Table,
      LeanCompCert.Ports.Section413G1Generated99999Chunks.expected99999,
      LeanCompCert.Ports.Section413G1Generated99999Chunks.words99999,
      LeanCompCert.Ports.Section413G1TableProgram.cellsOfWords]
  · have h := congrFun
      LeanCompCert.Ports.Section413WindowDirectTables.expectedG1_eq_direct 0
    simpa [g1Table,
      LeanCompCert.Ports.Section413WindowDirectTables.directG1,
      LeanCompCert.Ports.Section413G1Generated99999Chunks.wordAt,
      LeanCompCert.Ports.Section413Cells.decodeZ_zero, czero] using h
  · intro X hX1 hXN
    exact
      LeanCompCert.Ports.Section413G1Full99999Certificate.expected99999_pointwise
        X hX1 hXN
  · simp [g2Table,
      LeanCompCert.Ports.Section413G2Generated99999Chunks.expected99999,
      LeanCompCert.Ports.Section413G2Generated99999Chunks.words99999,
      LeanCompCert.Ports.Section413G2TableProgram.cellsOfWords]
  · have h := congrFun
      LeanCompCert.Ports.Section413WindowDirectTables.expectedG2_eq_direct 0
    simpa [g2Table,
      LeanCompCert.Ports.Section413WindowDirectTables.directG2,
      LeanCompCert.Ports.Section413G2Generated99999Chunks.wordAt,
      LeanCompCert.Ports.Section413Cells.decodeZ_zero, czero] using h
  · intro X hX1 hXN
    exact
      LeanCompCert.Ports.Section413G2Full99999Certificate.expected99999_pointwise
        X hX1 hXN
  · exact window_table_ok

end LeanCompCert.Ports.Section413Window99999Certificate

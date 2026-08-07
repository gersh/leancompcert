import LeanCompCert.Ports.ArraySegMobiusRootWrite
import LeanCompCert.Ports.ArraySegMobiusPrimeTable

/-!
# Machine representation of the segmented Möbius prime table

The production array stores the growing prime list consecutively at
`Cfg.primeBase`; `rWrite` points immediately after the represented prefix.
These structural lemmas lift the already-verified single root store to an
exact list append while framing every earlier table cell.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPrimeTableRep

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusPrimeInvariant
open LeanCompCert.Ports.ArraySegMobiusPrimeTable

/-- A list represented by consecutive array cells beginning at `base`. -/
def TablePrefix (arr : Nat → Nat) (base : Nat) : List Nat → Prop
  | [] => True
  | p :: ps => arr base = p ∧ TablePrefix arr (base + 1) ps

/-- Writing immediately after a represented prefix appends one value, provided
all earlier cells are framed. -/
theorem TablePrefix.append_single {arr arr' : Nat → Nat} {base n : Nat}
    {ps : List Nat}
    (hPrefix : TablePrefix arr base ps)
    (hWrite : arr' (base + ps.length) = n)
    (hFrame : ∀ x, x ≠ base + ps.length → arr' x = arr x) :
    TablePrefix arr' base (ps ++ [n]) := by
  induction ps generalizing base with
  | nil =>
      simpa [TablePrefix] using hWrite
  | cons p ps ih =>
      change arr' base = p ∧ TablePrefix arr' (base + 1) (ps ++ [n])
      constructor
      · rw [hFrame]
        · exact hPrefix.1
        · simp
      · apply ih hPrefix.2
        · rw [show (base + 1) + ps.length =
              base + (ps.length + 1) by omega]
          exact hWrite
        · intro x hx
          apply hFrame x
          intro heq
          apply hx
          rw [show (base + 1) + ps.length =
            base + (p :: ps).length by simp; omega]
          exact heq

/-- Pointwise framing below the end of a represented prefix preserves it. -/
theorem TablePrefix.frame_below {arr arr' : Nat → Nat} {base : Nat}
    {ps : List Nat}
    (hPrefix : TablePrefix arr base ps)
    (hFrame : ∀ x, x < base + ps.length → arr' x = arr x) :
    TablePrefix arr' base ps := by
  induction ps generalizing base with
  | nil => trivial
  | cons p ps ih =>
      constructor
      · rw [hFrame]
        · exact hPrefix.1
        · simp
      · apply ih hPrefix.2
        intro x hx
        apply hFrame x
        rw [show base + (p :: ps).length =
          (base + 1) + ps.length by simp; omega]
        exact hx

/-- Pointwise framing at the represented cells is sufficient; unlike
`frame_below`, this form does not ask for unrelated cells below `base`. -/
theorem TablePrefix.frame_cells {arr arr' : Nat → Nat} {base : Nat}
    {ps : List Nat}
    (hPrefix : TablePrefix arr base ps)
    (hFrame : ∀ k, k < ps.length →
      arr' (base + k) = arr (base + k)) :
    TablePrefix arr' base ps := by
  induction ps generalizing base with
  | nil => trivial
  | cons p ps ih =>
      constructor
      · simpa using (hFrame 0 (by simp)).trans hPrefix.1
      · apply ih hPrefix.2
        intro k hk
        have h := hFrame (k + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- A property of every represented list member holds at every represented
array cell. -/
theorem TablePrefix.cell_property {arr : Nat → Nat} {base : Nat}
    {ps : List Nat} {P : Nat → Prop}
    (hPrefix : TablePrefix arr base ps)
    (hall : ∀ p, p ∈ ps → P p)
    (k : Nat) (hk : k < ps.length) :
    P (arr (base + k)) := by
  induction ps generalizing base k with
  | nil => simp at hk
  | cons p ps ih =>
      cases k with
      | zero =>
          simpa [hPrefix.1] using hall p (by simp)
      | succ k =>
          have htail : ∀ q, q ∈ ps → P q := by
            intro q hq
            exact hall q (by simp [hq])
          have h := ih hPrefix.2 htail k (by simpa using hk)
          rw [show base + (k + 1) = (base + 1) + k by omega]
          exact h

/-- A represented append contains its represented left prefix. -/
theorem TablePrefix.of_append_left {arr : Nat → Nat} {base : Nat}
    {ps qs : List Nat}
    (hPrefix : TablePrefix arr base (ps ++ qs)) :
    TablePrefix arr base ps := by
  induction ps generalizing base with
  | nil => trivial
  | cons p ps ih =>
      constructor
      · exact hPrefix.1
      · exact ih hPrefix.2

/-- The concrete array prefix and live write cursor represent `ps`. -/
structure MachineTableRep (c : Cfg) (s : AState) (ps : List Nat) : Prop where
  table : TablePrefix s.arr c.primeBase ps
  cursor : s.regs rWrite = c.primeBase + ps.length
  guard : s.arr (c.primeBase + c.tableLen) = c.sentinel

theorem MachineTableRep.guard_pos {c : Cfg} {s : AState} {ps : List Nat}
    (hRep : MachineTableRep c s ps) :
    0 < s.arr (c.primeBase + c.tableLen) := by
  rw [hRep.guard]
  simp [Cfg.sentinel]

/-- Every represented non-guard table cell contains a prime. -/
theorem MachineTableRep.cell_prime {c : Cfg} {s : AState} {ps : List Nat}
    {bound k : Nat}
    (hRep : MachineTableRep c s ps)
    (hInv : PrimeTableInv ps bound)
    (hk : k < ps.length) :
    IsPrime (s.arr (c.primeBase + k)) :=
  TablePrefix.cell_property hRep.table hInv.sound k hk

/-- Uniform word bounds for every represented prime cell, derived from the
mathematical prime-table invariant. -/
theorem MachineTableRep.cell_bounds {c : Cfg} {s : AState} {ps : List Nat}
    {bound k : Nat}
    (hRep : MachineTableRep c s ps)
    (hInv : PrimeTableInv ps bound)
    (hk : k < ps.length)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M) :
    0 < s.arr (c.primeBase + k) ∧
      s.arr (c.primeBase + k) < M ∧
      s.arr (c.primeBase + k) * s.arr (c.primeBase + k) < M := by
  have hp := hRep.cell_prime hInv hk
  have hupper : s.arr (c.primeBase + k) ≤ bound :=
    TablePrefix.cell_property hRep.table hInv.upper k hk
  refine ⟨by have := hp.1; omega, by omega, ?_⟩
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hupper hupper) hboundSqM

/-- The verified collection suffix turns a represented prefix into its exact
append and advances the represented cursor. -/
theorem rootWriteSuffix_append (c : Cfg) (idx : Nat) (s : AState)
    (ps : List Nat) (n : Nat)
    (hRep : MachineTableRep c s ps)
    (hFit : ps.length < c.tableLen)
    (h65 : s.regs 65 = n)
    (h67 : s.regs 67 = 1)
    (h132 : s.regs 132 = 1)
    (hn2 : 2 ≤ n)
    (hnCap : n ≤ c.rootCap)
    (hnM : n < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    MachineTableRep c (arun idx s (rootWriteSuffix c)) (ps ++ [n]) := by
  let write := c.primeBase + ps.length
  have hWrite : s.regs rWrite = write := by
    simpa [write] using hRep.cursor
  have hsinkM : c.primeSink < M := by
    simp only [Cfg.arrayLen, Cfg.primeSink] at hA ⊢
    omega
  have hnextM : write + 1 < M := by
    have hnextA : write + 1 < c.arrayLen := by
      dsimp [write]
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hFit ⊢
      omega
    exact Nat.lt_trans hnextA hA
  have hout := arun_rootWriteSuffix_collect c idx s n write c.primeSink
    h65 h67 h132 hWrite rfl hn2 hnCap hnM hcapM hsinkM hnextM
  constructor
  · apply TablePrefix.append_single hRep.table
    · simpa [write] using hout.1
    · intro x hx
      apply arun_rootWriteSuffix_collect_frame c idx s n write c.primeSink x
        h65 h67 h132 hWrite rfl hn2 hnCap hnM hcapM hsinkM hnextM
      simpa [write] using hx
  · calc
      (arun idx s (rootWriteSuffix c)).regs rWrite = write + 1 := hout.2
      _ = c.primeBase + (ps ++ [n]).length := by simp [write]; omega
  · rw [arun_rootWriteSuffix_collect_frame c idx s n write c.primeSink
      (c.primeBase + c.tableLen) h65 h67 h132 hWrite rfl hn2 hnCap hnM
      hcapM hsinkM hnextM]
    · exact hRep.guard
    · simp only [write]
      omega

/-- A disabled collection store is redirected past the table and therefore
preserves the represented prefix and cursor. -/
theorem rootWriteSuffix_retain (c : Cfg) (idx : Nat) (s : AState)
    (ps : List Nat)
    (hRep : MachineTableRep c s ps)
    (hLen : ps.length ≤ c.tableLen)
    (h67 : s.regs 67 = 0)
    (hA : c.arrayLen < M) :
    MachineTableRep c (arun idx s (rootWriteSuffix c)) ps := by
  let write := c.primeBase + ps.length
  have hWrite : s.regs rWrite = write := by
    simpa [write] using hRep.cursor
  have hwriteM : write < M := by
    have hwriteA : write < c.arrayLen := by
      dsimp [write]
      simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
        Cfg.tableLen] at hLen ⊢
      omega
    exact Nat.lt_trans hwriteA hA
  have hbaseNe : c.primeBase ≠ c.primeSink := by
    simp only [Cfg.primeBase, Cfg.primeSink, Cfg.resultBase]
    omega
  have hcursor := (arun_rootWriteSuffix_marked_preserves c idx s write
    c.primeBase h67 hWrite hwriteM hA hbaseNe).2
  constructor
  · apply TablePrefix.frame_below hRep.table
    intro x hx
    have hxNe : x ≠ c.primeSink := by
      simp only [Cfg.primeBase, Cfg.primeSink, Cfg.resultBase,
        Cfg.tableLen] at hx hLen ⊢
      omega
    exact (arun_rootWriteSuffix_marked_preserves c idx s write x h67
      hWrite hwriteM hA hxNe).1
  · exact hcursor
  · have hendNe : c.primeBase + c.tableLen ≠ c.primeSink := by
      simp only [Cfg.primeBase, Cfg.primeSink, Cfg.resultBase]
      omega
    exact (arun_rootWriteSuffix_marked_preserves c idx s write
      (c.primeBase + c.tableLen) h67 hWrite hwriteM hA hendNe).1.trans
        hRep.guard

/-- The complete reusable root-table invariant: a concrete represented prefix
that is exactly the increasing list of primes through `bound`. -/
structure RootTableInv (c : Cfg) (s : AState) (ps : List Nat)
    (bound : Nat) : Prop extends MachineTableRep c s ps where
  primeTable : PrimeTableInv ps bound

/-- One live root-store branch preserves the complete represented prime-table
invariant for the next sequential candidate. -/
theorem RootTableInv.append_next (c : Cfg) (idx : Nat) (s : AState)
    (ps : List Nat) (bound n : Nat)
    (hInv : RootTableInv c s ps bound)
    (hFit : ps.length < c.tableLen)
    (hnext : n = bound + 1)
    (hunmarked : UnmarkedBy ps n)
    (h65 : s.regs 65 = n)
    (h67 : s.regs 67 = 1)
    (h132 : s.regs 132 = 1)
    (hn2 : 2 ≤ n)
    (hnCap : n ≤ c.rootCap)
    (hnM : n < M)
    (hcapM : c.rootCap < M)
    (hA : c.arrayLen < M) :
    RootTableInv c (arun idx s (rootWriteSuffix c)) (ps ++ [n]) n := by
  constructor
  · exact rootWriteSuffix_append c idx s ps n hInv.toMachineTableRep hFit
      h65 h67 h132 hn2 hnCap hnM hcapM hA
  · exact append_next_of_unmarked hInv.primeTable hnext hn2 hunmarked

/-- One marked root-store branch preserves the concrete table while advancing
the processed bound by one. -/
theorem RootTableInv.retain_next (c : Cfg) (idx : Nat) (s : AState)
    (ps : List Nat) (bound n : Nat)
    (hInv : RootTableInv c s ps bound)
    (hLen : ps.length ≤ c.tableLen)
    (hnext : n = bound + 1)
    (hmarked : ¬UnmarkedBy ps n)
    (h67 : s.regs 67 = 0)
    (hn2 : 2 ≤ n)
    (hA : c.arrayLen < M) :
    RootTableInv c (arun idx s (rootWriteSuffix c)) ps n := by
  constructor
  · exact rootWriteSuffix_retain c idx s ps hInv.toMachineTableRep hLen h67 hA
  · exact retain_next_of_marked hInv.primeTable hnext hn2 hmarked

end LeanCompCert.Ports.ArraySegMobiusPrimeTableRep

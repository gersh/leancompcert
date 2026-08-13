import LeanCompCert.Ports.Section413WindowPipelineSound
import LeanCompCert.Ports.Section413WindowPairingBridge

/-!
# Producer tables equal the paper reference functions

The rolled producers retain their tables as machine words.  This module
decodes one symbolic table index at a time and relates it to the corresponding
`g1Prefix`/`g2Prefix` cell.  It also proves the adjacent table difference is
inside the signed encoding range.  No concrete table or production loop is
evaluated in Lean.
-/

namespace LeanCompCert.Ports.Section413WindowTableReferenceBridge

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowEventScanner
open LeanCompCert.Ports.Section413WindowPipelineSound

def WithinCap (z : Cell) : Prop :=
  -(LeanCompCert.Ports.Section413G1Program.CAP : Int) ≤ z.lo ∧
    z.lo ≤ (LeanCompCert.Ports.Section413G1Program.CAP : Int) ∧
    -(LeanCompCert.Ports.Section413G1Program.CAP : Int) ≤ z.hi ∧
    z.hi ≤ (LeanCompCert.Ports.Section413G1Program.CAP : Int)

private theorem withinCap_zero : WithinCap czero := by
  simp [WithinCap, czero, LeanCompCert.Ports.Section413G1Program.CAP]

private theorem csub_signed_range {a b : Cell}
    (ha : WithinCap a) (hb : WithinCap b) :
    -((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) < (csub a b).lo ∧
      (csub a b).lo <
        ((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) ∧
      -((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) <
        (csub a b).hi ∧
      (csub a b).hi <
        ((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) := by
  rcases a with ⟨alo, ahi⟩
  rcases b with ⟨blo, bhi⟩
  simp only [WithinCap, csub, cadd, cneg] at ha hb ⊢
  have hcap :
      (2 * LeanCompCert.Ports.Section413G1Program.CAP : Nat) <
        LeanCompCert.Ports.Section413Cells.H63 := by decide
  have hcapInt :
      (2 : Int) * (LeanCompCert.Ports.Section413G1Program.CAP : Int) <
        (LeanCompCert.Ports.Section413Cells.H63 : Int) := by
    exact_mod_cast hcap
  omega

def g1G (X : Nat) : Cell :=
  if X ≤ g1TableCfg.cap then
    (LeanCompCert.Ports.Section413G1Sound.g1Prefix
      g1TableCfg.rounds g1TableCfg.checkLo g1TableCfg.cap X).g
  else czero

def g2G (X : Nat) : Cell :=
  if X ≤ g2TableCfg.cap then
    (LeanCompCert.Ports.Section413G2Sound.g2Prefix
      g2TableCfg.rounds g2TableCfg.checkLo g2TableCfg.cap X).g
  else czero

theorem g1_flag_zero
    (hzero : (LeanCompCert.Ports.Section413G1TableProgram.rawFinal
      g1TableCfg).regs LeanCompCert.Ports.Section413G1Program.rViol = 0) :
    g1TableCfg.tFlag = 0 := by
  have hcore := LeanCompCert.Ports.Section413G1TableSound.rawFinal_core_tRun
    g1TableCfg g1TableCfg_admissible
  rw [LeanCompCert.Ports.Section413G1Program.Cfg.tFlag]
  exact hcore.1.symm.trans hzero

theorem g2_flag_zero
    (hzero : (LeanCompCert.Ports.Section413G2TableProgram.rawFinal
      g2TableCfg).regs LeanCompCert.Ports.Section413G2Program.rViol = 0) :
    g2TableCfg.tFlag = 0 := by
  have hcore := LeanCompCert.Ports.Section413G2TableSound.rawFinal_core_tRun
    g2TableCfg g2TableCfg_admissible
  rw [LeanCompCert.Ports.Section413G2Program.Cfg.tFlag]
  exact hcore.1.symm.trans hzero

set_option maxRecDepth 10000 in
theorem g1_tableCell_eq (hflag : g1TableCfg.tFlag = 0)
    (X : Nat) (hX : X ≤ g1TableCfg.cap) :
    tableCell g1TableCfg.cap
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr X =
        g1G X := by
  rcases Nat.eq_zero_or_pos X with rfl | hpos
  · have hz := LeanCompCert.Ports.Section413G1TableSound.rawFinal_zero_cells
      g1TableCfg g1TableCfg_admissible
    calc
      tableCell g1TableCfg.cap
          (LeanCompCert.Ports.Section413G1TableProgram.rawFinal
            g1TableCfg).arr 0 = czero := by
        apply (Cell.mk.injEq _ _ _ _).mpr
        constructor
        · simpa only [tableCell, Nat.add_zero,
            show LeanCompCert.Ports.Section413WindowTableRead.tableLo
                g1TableCfg.cap =
              LeanCompCert.Ports.Section413G1TableProgram.tableLo
                g1TableCfg by rfl,
            hz.1, LeanCompCert.Ports.Section413Cells.decodeZ_zero] using rfl
        · simpa only [tableCell, Nat.add_zero,
            show LeanCompCert.Ports.Section413WindowTableRead.tableHi
                g1TableCfg.cap =
              LeanCompCert.Ports.Section413G1TableProgram.tableHi
                g1TableCfg by rfl,
            hz.2, LeanCompCert.Ports.Section413Cells.decodeZ_zero] using rfl
      _ = g1G 0 := by
        simp [g1G, LeanCompCert.Ports.Section413G1Sound.g1Prefix_zero,
          czero]
  · have hraw := LeanCompCert.Ports.Section413G1TableSound.rawFinal_cell
      g1TableCfg g1TableCfg_admissible g1TableCfg_sound X hpos hX
    have hrel := LeanCompCert.Ports.Section413G1Sound.sweep_prefix
      g1TableCfg g1TableCfg_sound hflag X hX
    apply (Cell.mk.injEq _ _ _ _).mpr
    constructor
    · have hg := congrArg Cell.lo hrel.g_eq
      change LeanCompCert.Ports.Section413Cells.decodeZ
          ((LeanCompCert.Ports.Section413G1TableProgram.rawFinal
            g1TableCfg).arr
            (LeanCompCert.Ports.Section413WindowTableRead.tableLo
              g1TableCfg.cap + X)) = (g1G X).lo
      rw [show LeanCompCert.Ports.Section413WindowTableRead.tableLo
            g1TableCfg.cap =
          LeanCompCert.Ports.Section413G1TableProgram.tableLo g1TableCfg by rfl,
        hraw.1]
      simpa [g1G, hX] using hg
    · have hg := congrArg Cell.hi hrel.g_eq
      change LeanCompCert.Ports.Section413Cells.decodeZ
          ((LeanCompCert.Ports.Section413G1TableProgram.rawFinal
            g1TableCfg).arr
            (LeanCompCert.Ports.Section413WindowTableRead.tableHi
              g1TableCfg.cap + X)) = (g1G X).hi
      rw [show LeanCompCert.Ports.Section413WindowTableRead.tableHi
            g1TableCfg.cap =
          LeanCompCert.Ports.Section413G1TableProgram.tableHi g1TableCfg by rfl,
        hraw.2]
      simpa [g1G, hX] using hg

set_option maxRecDepth 10000 in
theorem g2_tableCell_eq (hflag : g2TableCfg.tFlag = 0)
    (X : Nat) (hX : X ≤ g2TableCfg.cap) :
    tableCell g2TableCfg.cap
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr X =
        g2G X := by
  rcases Nat.eq_zero_or_pos X with rfl | hpos
  · have hz := LeanCompCert.Ports.Section413G2TableSound.rawFinal_zero_cells
      g2TableCfg g2TableCfg_admissible
    calc
      tableCell g2TableCfg.cap
          (LeanCompCert.Ports.Section413G2TableProgram.rawFinal
            g2TableCfg).arr 0 = czero := by
        apply (Cell.mk.injEq _ _ _ _).mpr
        constructor
        · simpa only [tableCell, Nat.add_zero,
            show LeanCompCert.Ports.Section413WindowTableRead.tableLo
                g2TableCfg.cap =
              LeanCompCert.Ports.Section413G2TableProgram.tableLo
                g2TableCfg by rfl,
            hz.1, LeanCompCert.Ports.Section413Cells.decodeZ_zero] using rfl
        · simpa only [tableCell, Nat.add_zero,
            show LeanCompCert.Ports.Section413WindowTableRead.tableHi
                g2TableCfg.cap =
              LeanCompCert.Ports.Section413G2TableProgram.tableHi
                g2TableCfg by rfl,
            hz.2, LeanCompCert.Ports.Section413Cells.decodeZ_zero] using rfl
      _ = g2G 0 := by
        simp [g2G, LeanCompCert.Ports.Section413G2Sound.g2Prefix_zero,
          czero]
  · have hraw := LeanCompCert.Ports.Section413G2TableSound.rawFinal_cell
      g2TableCfg g2TableCfg_admissible g2TableCfg_sound X hpos hX
    have hrel := LeanCompCert.Ports.Section413G2Sound.sweep_prefix
      g2TableCfg g2TableCfg_sound hflag X hX
    apply (Cell.mk.injEq _ _ _ _).mpr
    constructor
    · have hg := congrArg Cell.lo hrel.g_eq
      change LeanCompCert.Ports.Section413Cells.decodeZ
          ((LeanCompCert.Ports.Section413G2TableProgram.rawFinal
            g2TableCfg).arr
            (LeanCompCert.Ports.Section413WindowTableRead.tableLo
              g2TableCfg.cap + X)) = (g2G X).lo
      rw [show LeanCompCert.Ports.Section413WindowTableRead.tableLo
            g2TableCfg.cap =
          LeanCompCert.Ports.Section413G2TableProgram.tableLo g2TableCfg by rfl,
        hraw.1]
      simpa [g2G, hX] using hg
    · have hg := congrArg Cell.hi hrel.g_eq
      change LeanCompCert.Ports.Section413Cells.decodeZ
          ((LeanCompCert.Ports.Section413G2TableProgram.rawFinal
            g2TableCfg).arr
            (LeanCompCert.Ports.Section413WindowTableRead.tableHi
              g2TableCfg.cap + X)) = (g2G X).hi
      rw [show LeanCompCert.Ports.Section413WindowTableRead.tableHi
            g2TableCfg.cap =
          LeanCompCert.Ports.Section413G2TableProgram.tableHi g2TableCfg by rfl,
        hraw.2]
      simpa [g2G, hX] using hg

theorem g1_tableCell_withinCap (hflag : g1TableCfg.tFlag = 0)
    (X : Nat) (hX : X ≤ g1TableCfg.cap) :
    WithinCap (tableCell g1TableCfg.cap
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr X) := by
  rcases Nat.eq_zero_or_pos X with rfl | hpos
  · rw [g1_tableCell_eq hflag 0 (by omega)]
    simpa [g1G, LeanCompCert.Ports.Section413G1Sound.g1Prefix_zero] using
      withinCap_zero
  · have hrel := LeanCompCert.Ports.Section413G1Sound.sweep_prefix
      g1TableCfg g1TableCfg_sound hflag X hX
    have hlo := LeanCompCert.Ports.Section413G1Sound.capped_range
      hrel.gLo_u64 hrel.gLo_cap
    have hhi := LeanCompCert.Ports.Section413G1Sound.capped_range
      hrel.gHi_u64 hrel.gHi_cap
    rw [g1_tableCell_eq hflag X hX]
    rw [g1G, if_pos hX, ← hrel.g_eq]
    exact ⟨hlo.1, hlo.2, hhi.1, hhi.2⟩

theorem g2_tableCell_withinCap (hflag : g2TableCfg.tFlag = 0)
    (X : Nat) (hX : X ≤ g2TableCfg.cap) :
    WithinCap (tableCell g2TableCfg.cap
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr X) := by
  rcases Nat.eq_zero_or_pos X with rfl | hpos
  · rw [g2_tableCell_eq hflag 0 (by omega)]
    simpa [g2G, LeanCompCert.Ports.Section413G2Sound.g2Prefix_zero] using
      withinCap_zero
  · have hrel := LeanCompCert.Ports.Section413G2Sound.sweep_prefix
      g2TableCfg g2TableCfg_sound hflag X hX
    have hlo := LeanCompCert.Ports.Section413G2Sound.capped_range
      hrel.gLo_u64 hrel.gLo_cap
    have hhi := LeanCompCert.Ports.Section413G2Sound.capped_range
      hrel.gHi_u64 hrel.gHi_cap
    rw [g2_tableCell_eq hflag X hX]
    rw [g2G, if_pos hX, ← hrel.g_eq]
    exact ⟨hlo.1, hlo.2, hhi.1, hhi.2⟩

private theorem safeX_le {cap x : Nat} (hcap : 1 ≤ cap) (hx : x ≤ cap) :
    LeanCompCert.Ports.Section413WindowTableRead.safeX x ≤ cap := by
  by_cases hzero : x = 0
  · simp [LeanCompCert.Ports.Section413WindowTableRead.safeX, hzero, hcap]
  · simp [LeanCompCert.Ports.Section413WindowTableRead.safeX, hzero, hx]

theorem g1_tableDiff_eq_and_range (hflag : g1TableCfg.tFlag = 0)
    (x : Nat) (hx : x ≤ g1TableCfg.cap) :
    let y := LeanCompCert.Ports.Section413WindowTableRead.safeX x
    let d := tableDiff g1TableCfg.cap
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr x
    d = csub (g1G (y - 1)) (g1G y) ∧
      -((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) < d.lo ∧
      d.lo < ((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) ∧
      -((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) < d.hi ∧
      d.hi < ((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) := by
  dsimp only
  let y := LeanCompCert.Ports.Section413WindowTableRead.safeX x
  have hy : y ≤ g1TableCfg.cap := safeX_le (by decide) hx
  have hym : y - 1 ≤ g1TableCfg.cap := Nat.le_trans (Nat.sub_le _ _) hy
  have heq0 := g1_tableCell_eq hflag (y - 1) hym
  have heq1 := g1_tableCell_eq hflag y hy
  have hrange := csub_signed_range
    (g1_tableCell_withinCap hflag (y - 1) hym)
    (g1_tableCell_withinCap hflag y hy)
  unfold tableDiff
  change csub (tableCell g1TableCfg.cap _ (y - 1))
      (tableCell g1TableCfg.cap _ y) = _ ∧ _
  rw [heq0, heq1]
  exact ⟨rfl, hrange⟩

theorem g2_tableDiff_eq_and_range (hflag : g2TableCfg.tFlag = 0)
    (x : Nat) (hx : x ≤ g2TableCfg.cap) :
    let y := LeanCompCert.Ports.Section413WindowTableRead.safeX x
    let d := tableDiff g2TableCfg.cap
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr x
    d = csub (g2G (y - 1)) (g2G y) ∧
      -((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) < d.lo ∧
      d.lo < ((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) ∧
      -((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) < d.hi ∧
      d.hi < ((LeanCompCert.Ports.Section413Cells.H63 : Nat) : Int) := by
  dsimp only
  let y := LeanCompCert.Ports.Section413WindowTableRead.safeX x
  have hy : y ≤ g2TableCfg.cap := safeX_le (by decide) hx
  have hym : y - 1 ≤ g2TableCfg.cap := Nat.le_trans (Nat.sub_le _ _) hy
  have heq0 := g2_tableCell_eq hflag (y - 1) hym
  have heq1 := g2_tableCell_eq hflag y hy
  have hrange := csub_signed_range
    (g2_tableCell_withinCap hflag (y - 1) hym)
    (g2_tableCell_withinCap hflag y hy)
  unfold tableDiff
  change csub (tableCell g2TableCfg.cap _ (y - 1))
      (tableCell g2TableCfg.cap _ y) = _ ∧ _
  rw [heq0, heq1]
  exact ⟨rfl, hrange⟩

#print axioms g1_tableDiff_eq_and_range
#print axioms g2_tableDiff_eq_and_range

end LeanCompCert.Ports.Section413WindowTableReferenceBridge

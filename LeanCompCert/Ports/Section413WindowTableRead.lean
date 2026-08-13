/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowSchedule

/-!
# Direct compiled reads from a Section 4.1.3 producer table

The rolled window scanner consumes the G-table planes in memory.  A zero
quotient can occur only on an inactive schedule slot; `prepStage` clamps it
to one so even speculative branchless loads remain in bounds.  The eventual
contribution is gated to zero.  No table cell is materialised in Lean.
-/

namespace LeanCompCert.Ports.Section413WindowTableRead

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.BlockDefined

def tableLo (cap : Nat) : Nat := 3 * (cap + 1)
def tableHi (cap : Nat) : Nat := 4 * (cap + 1)
def tableLen (cap : Nat) : Nat := 5 * (cap + 1)

def rX : Nat := 17
def rNZ : Nat := 18
def rInv : Nat := 19
def rSafe : Nat := 20
def rPrev : Nat := 21
def rAddrPrevLo : Nat := 22
def rAddrPrevHi : Nat := 23
def rAddrCurLo : Nat := 24
def rAddrCurHi : Nat := 25
def rPrevLo : Nat := 26
def rPrevHi : Nat := 27
def rCurLo : Nat := 28
def rCurHi : Nat := 29
def rDiffLo : Nat := 30
def rDiffHi : Nat := 31

def prepStage (cap : Nat) : List Instr :=
  [ .binop rNZ .ne (.reg rX) (.lit 0)
  , .binop rInv .eq (.reg rX) (.lit 0)
  , .binop rSafe .add (.reg rX) (.reg rInv)
  , .binop rPrev .sub (.reg rSafe) (.lit 1)
  , .binop rAddrPrevLo .add (.reg rPrev) (.lit (tableLo cap))
  , .binop rAddrPrevHi .add (.reg rPrev) (.lit (tableHi cap))
  , .binop rAddrCurLo .add (.reg rSafe) (.lit (tableLo cap))
  , .binop rAddrCurHi .add (.reg rSafe) (.lit (tableHi cap)) ]

def loadStage : List AInstr :=
  [ .load rPrevLo rAddrPrevLo
  , .load rPrevHi rAddrPrevHi
  , .load rCurLo rAddrCurLo
  , .load rCurHi rAddrCurHi ]

def diffStage : List Instr :=
  [ .binop rDiffLo .sub (.reg rPrevLo) (.reg rCurHi)
  , .binop rDiffHi .sub (.reg rPrevHi) (.reg rCurLo) ]

def body (cap : Nat) : List AInstr :=
  lift (prepStage cap) ++ loadStage ++ lift diffStage

def safeX (x : Nat) : Nat := if x = 0 then 1 else x

theorem prepStage_outputs (k cap : Nat) (s : RegState)
    (hcapPos : 1 ≤ cap) (htable : tableLen cap < M) (hx : s rX ≤ cap) :
    let out := srun k s (prepStage cap)
    out rSafe = safeX (s rX) ∧
      out rPrev = safeX (s rX) - 1 ∧
      out rAddrPrevLo = tableLo cap + (safeX (s rX) - 1) ∧
      out rAddrPrevHi = tableHi cap + (safeX (s rX) - 1) ∧
      out rAddrCurLo = tableLo cap + safeX (s rX) ∧
      out rAddrCurHi = tableHi cap + safeX (s rX) := by
  dsimp only
  simp only [rX, rNZ, rInv, rSafe, rPrev, rAddrPrevLo, rAddrPrevHi,
    rAddrCurLo, rAddrCurHi] at hx ⊢
  simp only [prepStage, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rX, rNZ, rInv, rSafe, rPrev, rAddrPrevLo, rAddrPrevHi,
    rAddrCurLo, rAddrCurHi]
  simp only [Nat.reduceEqDiff, if_false, if_true,
    show 0 % M = 0 by decide, show 1 % M = 1 by decide]
  have hcap : cap < M := by
    have : cap < tableLen cap := by simp [tableLen]; omega
    omega
  have hlo : tableLo cap + cap < M := by
    have : tableLo cap + cap < tableLen cap := by
      simp [tableLo, tableLen]; omega
    omega
  have hhi : tableHi cap + cap < M := by
    have : tableHi cap + cap < tableLen cap := by
      simp [tableHi, tableLen]; omega
    omega
  have hlo0 : tableLo cap < M := by
    have : tableLo cap < tableLen cap := by simp [tableLo, tableLen]
    omega
  have hhi0 : tableHi cap < M := by
    have : tableHi cap < tableLen cap := by simp [tableHi, tableLen]
    omega
  by_cases hzero : s 17 = 0
  · have hLo1 : tableLo cap + 1 < M := by
      have : tableLo cap + 1 < tableLen cap := by
        unfold tableLo tableLen
        omega
      omega
    have hHi1 : tableHi cap + 1 < M := by
      have : tableHi cap + 1 < tableLen cap := by
        unfold tableHi tableLen
        omega
      omega
    have hLo1Mod : (1 + tableLo cap) % M = 1 + tableLo cap :=
      Nat.mod_eq_of_lt (by omega)
    have hHi1Mod : (1 + tableHi cap) % M = 1 + tableHi cap :=
      Nat.mod_eq_of_lt (by omega)
    simp [hzero, safeX, show (1 + (M - 1)) % M = 0 by decide,
      show 1 % M = 1 by decide, Nat.add_comm,
      Nat.mod_eq_of_lt hlo0, Nat.mod_eq_of_lt hhi0,
      hLo1Mod, hHi1Mod]
  · have hxpos : 0 < s 17 := Nat.pos_of_ne_zero hzero
    have hsM : s 17 < M := Nat.lt_of_le_of_lt hx hcap
    have hprevLo : tableLo cap + (s 17 - 1) < M := by omega
    have hprevHi : tableHi cap + (s 17 - 1) < M := by omega
    have hcurLo : tableLo cap + s 17 < M := by omega
    have hcurHi : tableHi cap + s 17 < M := by omega
    have hprev : (s 17 + (M - 1)) % M = s 17 - 1 := by
      rw [show s 17 + (M - 1) = (s 17 - 1) + M by omega,
        Nat.add_mod]
      simp [Nat.mod_eq_of_lt (by omega : s 17 - 1 < M)]
    have hprevLoMod : (s 17 - 1 + tableLo cap) % M =
        tableLo cap + (s 17 - 1) := by
      simpa [Nat.add_comm] using Nat.mod_eq_of_lt hprevLo
    have hprevHiMod : (s 17 - 1 + tableHi cap) % M =
        tableHi cap + (s 17 - 1) := by
      simpa [Nat.add_comm] using Nat.mod_eq_of_lt hprevHi
    have hcurLoMod : (s 17 + tableLo cap) % M = tableLo cap + s 17 := by
      simpa [Nat.add_comm] using Nat.mod_eq_of_lt hcurLo
    have hcurHiMod : (s 17 + tableHi cap) % M = tableHi cap + s 17 := by
      simpa [Nat.add_comm] using Nat.mod_eq_of_lt hcurHi
    simp [hzero, safeX, Nat.mod_eq_of_lt hsM,
      hprev, hprevLoMod, hprevHiMod, hcurLoMod, hcurHiMod]

theorem prep_addresses_bounded (k cap : Nat) (s : RegState)
    (hcapPos : 1 ≤ cap) (htable : tableLen cap < M) (hx : s rX ≤ cap) :
    let out := srun k s (prepStage cap)
    out rAddrPrevLo < tableLen cap ∧
      out rAddrPrevHi < tableLen cap ∧
      out rAddrCurLo < tableLen cap ∧
      out rAddrCurHi < tableLen cap := by
  dsimp only
  have h := prepStage_outputs k cap s hcapPos htable hx
  rcases h with ⟨_, _, hPrevLo, hPrevHi, hCurLo, hCurHi⟩
  rw [hPrevLo, hPrevHi, hCurLo, hCurHi]
  by_cases hzero : s rX = 0 <;>
    simp [safeX, hzero, tableLo, tableHi, tableLen] <;> omega

theorem loadStage_outputs (k : Nat) (s : AState) :
    let out := arun k s loadStage
    out.regs rPrevLo = s.arr (s.regs rAddrPrevLo) ∧
      out.regs rPrevHi = s.arr (s.regs rAddrPrevHi) ∧
      out.regs rCurLo = s.arr (s.regs rAddrCurLo) ∧
      out.regs rCurHi = s.arr (s.regs rAddrCurHi) ∧
      out.arr = s.arr := by
  dsimp only
  simp [loadStage, arun, astep, AState.writeReg, rPrevLo, rPrevHi,
    rCurLo, rCurHi, rAddrPrevLo, rAddrPrevHi, rAddrCurLo, rAddrCurHi]

theorem diffStage_outputs (k : Nat) (s : RegState) :
    let out := srun k s diffStage
    out rDiffLo = LeanCompCert.Ports.Section413G1Program.tsub
        (s rPrevLo) (s rCurHi) ∧
      out rDiffHi = LeanCompCert.Ports.Section413G1Program.tsub
        (s rPrevHi) (s rCurLo) := by
  dsimp only
  simp only [rDiffLo, rDiffHi, rPrevLo, rPrevHi, rCurLo, rCurHi] at ⊢
  simp only [diffStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rDiffLo, rDiffHi, rPrevLo, rPrevHi,
    rCurLo, rCurHi, Nat.reduceEqDiff, if_false, if_true]
  constructor <;> rfl

theorem body_defined (k cap : Nat) (s : AState)
    (hcapPos : 1 ≤ cap) (htable : tableLen cap < M)
    (hx : s.regs rX ≤ cap) :
    AllDefined (tableLen cap) k s (body cap) := by
  rw [body, List.append_assoc, AllDefined_append]
  refine ⟨(allDefined_lift _ _ _ _).mpr
    (sAllDefined_of_noDiv k (prepStage cap) s.regs
      (by simp [prepStage, NoDivI])), ?_⟩
  let p := arun k s (lift (prepStage cap))
  have hpArr : p.arr = s.arr := by simp [p, arun_lift]
  rw [AllDefined_append]
  refine ⟨?_, ?_⟩
  · have hb := prep_addresses_bounded k cap s.regs hcapPos htable hx
    simpa [loadStage, AllDefined, ADefined, astep, AState.writeReg,
      p, arun_lift, hpArr, rPrevLo, rPrevHi, rCurLo, rCurHi,
      rAddrPrevLo, rAddrPrevHi, rAddrCurLo, rAddrCurHi] using hb
  · exact (allDefined_lift _ _ _ _).mpr
      (sAllDefined_of_noDiv k diffStage
        (arun k p loadStage).regs (by decide))

theorem body_outputs (k cap : Nat) (s : AState)
    (hcapPos : 1 ≤ cap) (htable : tableLen cap < M)
    (hx : s.regs rX ≤ cap) :
    let out := arun k s (body cap)
    out.regs rDiffLo = LeanCompCert.Ports.Section413G1Program.tsub
        (s.arr (tableLo cap + (safeX (s.regs rX) - 1)))
        (s.arr (tableHi cap + safeX (s.regs rX))) ∧
      out.regs rDiffHi = LeanCompCert.Ports.Section413G1Program.tsub
        (s.arr (tableHi cap + (safeX (s.regs rX) - 1)))
        (s.arr (tableLo cap + safeX (s.regs rX))) ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s (lift (prepStage cap))
  let l := arun k p loadStage
  have hp := prepStage_outputs k cap s.regs hcapPos htable hx
  have hl := loadStage_outputs k p
  have hd := diffStage_outputs k l.regs
  have hpPrevLo : p.regs rAddrPrevLo =
      tableLo cap + (safeX (s.regs rX) - 1) := by
    simpa [p, arun_lift] using hp.2.2.1
  have hpPrevHi : p.regs rAddrPrevHi =
      tableHi cap + (safeX (s.regs rX) - 1) := by
    simpa [p, arun_lift] using hp.2.2.2.1
  have hpCurLo : p.regs rAddrCurLo =
      tableLo cap + safeX (s.regs rX) := by
    simpa [p, arun_lift] using hp.2.2.2.2.1
  have hpCurHi : p.regs rAddrCurHi =
      tableHi cap + safeX (s.regs rX) := by
    simpa [p, arun_lift] using hp.2.2.2.2.2
  have hpArr : p.arr = s.arr := by simp [p, arun_lift]
  rw [body, arun_append, arun_append, arun_lift]
  change srun k l.regs diffStage rDiffLo = _ ∧
    srun k l.regs diffStage rDiffHi = _ ∧ _
  rw [hd.1, hd.2, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1,
    hpPrevLo, hpPrevHi, hpCurLo, hpCurHi, hpArr]
  refine ⟨rfl, rfl, ?_⟩
  exact hl.2.2.2.2.trans hpArr

theorem body_outputs_encoded_diff (k cap : Nat) (s : AState)
    (hcapPos : 1 ≤ cap) (htable : tableLen cap < M)
    (hx : s.regs rX ≤ cap) (harr : ∀ j, s.arr j < M) :
    let x := safeX (s.regs rX)
    let out := arun k s (body cap)
    out.regs rDiffLo = LeanCompCert.Ports.Section413Cells.encodeZ
        (LeanCompCert.Ports.Section413Cells.decodeZ
            (s.arr (tableLo cap + (x - 1))) -
          LeanCompCert.Ports.Section413Cells.decodeZ
            (s.arr (tableHi cap + x))) ∧
      out.regs rDiffHi = LeanCompCert.Ports.Section413Cells.encodeZ
        (LeanCompCert.Ports.Section413Cells.decodeZ
            (s.arr (tableHi cap + (x - 1))) -
          LeanCompCert.Ports.Section413Cells.decodeZ
            (s.arr (tableLo cap + x))) ∧
      out.arr = s.arr := by
  dsimp only
  have h := body_outputs k cap s hcapPos htable hx
  rw [h.1, h.2.1]
  refine ⟨?_, ?_, h.2.2⟩
  · exact LeanCompCert.Ports.Section413G1Sound.tsub_eq_encodeZ _ _
      (harr _) (harr _)
  · exact LeanCompCert.Ports.Section413G1Sound.tsub_eq_encodeZ _ _
      (harr _) (harr _)

#print axioms prepStage_outputs
#print axioms prep_addresses_bounded
#print axioms loadStage_outputs
#print axioms diffStage_outputs
#print axioms body_defined
#print axioms body_outputs
#print axioms body_outputs_encoded_diff

end LeanCompCert.Ports.Section413WindowTableRead

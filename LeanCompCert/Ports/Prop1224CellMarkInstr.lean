import LeanCompCert.Ports.Prop1224CellMarkModel
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Literal front end of the Proposition 12.2.4 marker

The monolithic production block is split into small, definitionally equal
slices.  The lemmas below prove the phase, reset, and address denotations
without normalizing the remaining instructions or evaluating any marking
schedule.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def p1224MarkPhaseInstrs (c : CellCfg) : List Instr :=
  let L := c.segLen
  let T := c.markSteps
  [ .binop 10 .lt (.reg rR) (.lit T)
  , .binop 11 .lt (.reg rR) (.lit (T + L))
  , .binop 12 .sub (.reg 11) (.reg 10)
  , .binop 13 .sub (.lit 1) (.reg 11) ]

def p1224MarkPhaseBody (c : CellCfg) : List AInstr :=
  lift (p1224MarkPhaseInstrs c)

def p1224MarkResetInstrs (c : CellCfg) : List Instr :=
  let q0 := c.q0
  [ .binop 14 .eq (.reg rR) (.lit 0)
  , .binop 15 .sub (.lit 1) (.reg 14)
  , .binop 16 .urem (.reg rW) (.lit q0)
  , .binop 17 .sub (.lit q0) (.reg 16)
  , .binop 18 .urem (.reg 17) (.lit q0)
  , .binop rPi .mul (.reg 15) (.reg rPi)
  , .binop 19 .mul (.reg 14) (.lit q0)
  , .binop 20 .mul (.reg 15) (.reg rQp)
  , .binop rQp .add (.reg 19) (.reg 20)
  , .binop 21 .mul (.reg 15) (.reg rBp)
  , .binop rBp .add (.reg 19) (.reg 21)
  , .binop 22 .mul (.reg 15) (.reg rFs)
  , .binop rFs .add (.reg 14) (.reg 22)
  , .binop 23 .mul (.reg 14) (.reg 18)
  , .binop 24 .mul (.reg 15) (.reg rJ)
  , .binop rJ .add (.reg 23) (.reg 24) ]

def p1224MarkResetBody (c : CellCfg) : List AInstr :=
  lift (p1224MarkResetInstrs c)

def p1224MarkPreludeBody (c : CellCfg) : List AInstr :=
  p1224MarkPhaseBody c ++ p1224MarkResetBody c

def p1224MarkAddressInstrs (c : CellCfg) : List Instr :=
  let L := c.segLen
  let SNK := c.sink
  [ .binop 25 .lt (.reg rJ) (.lit L)
  , .binop 26 .mul (.reg 25) (.reg 10)
  , .binop 27 .sub (.lit 1) (.reg 26)
  , .binop 28 .mul (.reg 26) (.reg rJ)
  , .binop 29 .mul (.reg 27) (.lit SNK)
  , .binop 30 .add (.reg 28) (.reg 29)
  , .binop 31 .add (.reg 30) (.lit L)
  , .binop 32 .add (.reg 30) (.lit (2 * L)) ]

def p1224MarkAddressBody (c : CellCfg) : List AInstr :=
  lift (p1224MarkAddressInstrs c)

theorem p1224MarkPhaseBody_eq_slice (c : CellCfg) :
    c.markBody.take (p1224MarkPhaseBody c).length =
      p1224MarkPhaseBody c := by
  rfl

theorem p1224MarkResetBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 4).take (p1224MarkResetBody c).length =
      p1224MarkResetBody c := by
  rfl

theorem p1224MarkAddressBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 20).take (p1224MarkAddressBody c).length =
      p1224MarkAddressBody c := by
  rfl

theorem p1224MarkPhaseBody_active_run (c : CellCfg) (k : Nat)
    (s : AState) (r : Nat) (hr : s.regs rR = r)
    (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M) :
    let out := arun k s (p1224MarkPhaseBody c)
    out.regs 10 = 1 ∧ out.regs 11 = 1 ∧ out.regs 12 = 0 ∧
      out.regs 13 = 0 ∧ out.arr = s.arr := by
  have hTM : c.markSteps < M := by omega
  have hrTL : r < c.markSteps + c.segLen := by omega
  have h1M : (1 : Nat) < M := by decide
  have hzero : (1 + (M - 1)) % M = 0 := by decide
  have hr5 : s.regs 5 = r := by simpa [rR] using hr
  simp only [p1224MarkPhaseBody, arun_lift]
  simp [p1224MarkPhaseInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hr5, hrT, hrTL, hzero, rR,
    Nat.mod_eq_of_lt hTM, Nat.mod_eq_of_lt hperiod,
    Nat.mod_eq_of_lt h1M]

theorem p1224MarkResetBody_nonstart_run (c : CellCfg) (k : Nat)
    (s : AState) (r : Nat) (hr : s.regs rR = r) (hr0 : r ≠ 0)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : s.regs rPi < M) (hqM : s.regs rQp < M)
    (hbpM : s.regs rBp < M) (hfsM : s.regs rFs < M)
    (hjM : s.regs rJ < M) :
    let out := arun k s (p1224MarkResetBody c)
    out.regs rPi = s.regs rPi ∧ out.regs rQp = s.regs rQp ∧
      out.regs rBp = s.regs rBp ∧ out.regs rFs = s.regs rFs ∧
      out.regs rJ = s.regs rJ ∧ out.arr = s.arr := by
  have hr5 : s.regs 5 = r := by simpa [rR] using hr
  have hpi2M : s.regs 2 < M := by simpa [rPi] using hpiM
  have hq3M : s.regs 3 < M := by simpa [rQp] using hqM
  have hj4M : s.regs 4 < M := by simpa [rJ] using hjM
  have hbp170M : s.regs 170 < M := by simpa [rBp] using hbpM
  have hfs172M : s.regs 172 < M := by simpa [rFs] using hfsM
  have hq0nz : c.q0 ≠ 0 := Nat.ne_of_gt hq0
  have h1M : (1 : Nat) < M := by decide
  simp only [p1224MarkResetBody, arun_lift]
  simp [p1224MarkResetInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hr5, hr0, rPi, rQp, rJ, rR, rW, rBp,
    rFs, hq0nz, Nat.mod_eq_of_lt hq0M, Nat.mod_eq_of_lt hpi2M,
    Nat.mod_eq_of_lt hq3M, Nat.mod_eq_of_lt hbp170M,
    Nat.mod_eq_of_lt hfs172M, Nat.mod_eq_of_lt hj4M,
    Nat.mod_eq_of_lt h1M]

theorem p1224MarkResetBody_start_run (c : CellCfg) (k : Nat)
    (s : AState) (w : Nat) (hr : s.regs rR = 0)
    (hw : s.regs rW = w) (hq0 : 0 < c.q0) (hq0M : c.q0 < M) :
    let out := arun k s (p1224MarkResetBody c)
    out.regs rPi = 0 ∧ out.regs rQp = c.q0 ∧
      out.regs rBp = c.q0 ∧ out.regs rFs = 1 ∧
      out.regs rJ = p1224StartOffset w c.q0 ∧ out.arr = s.arr := by
  have hr5 : s.regs 5 = 0 := by simpa [rR] using hr
  have hw6 : s.regs 6 = w := by simpa [rW] using hw
  have hq0nz : c.q0 ≠ 0 := Nat.ne_of_gt hq0
  have hrem : w % c.q0 < c.q0 := Nat.mod_lt w hq0
  have hremM : w % c.q0 < M := by omega
  have hoffQ : p1224StartOffset w c.q0 < c.q0 := by
    unfold p1224StartOffset
    exact Nat.mod_lt _ hq0
  have hoffM : p1224StartOffset w c.q0 < M := by omega
  have hoffRawM : (c.q0 - w % c.q0) % c.q0 < M := by
    simpa [p1224StartOffset] using hoffM
  have hsubM :
      (c.q0 + (M - w % c.q0)) % M = c.q0 - w % c.q0 := by
    by_cases hz : w % c.q0 = 0
    · simp [hz, Nat.mod_eq_of_lt hq0M]
    · have hdelta : c.q0 - w % c.q0 < M := by omega
      have heq : c.q0 + (M - w % c.q0) =
          M + (c.q0 - w % c.q0) := by omega
      rw [heq, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hdelta]
  have h1M : (1 : Nat) < M := by decide
  have hsubOne : 1 + (M - 1) = M := by omega
  simp only [p1224MarkResetBody, arun_lift]
  simp [p1224MarkResetInstrs, p1224StartOffset, srun, RegState.set,
    sdest, sval, denoteOperand, denoteOp, hr5, hw6, rPi, rQp, rJ, rR,
    rW, rBp, rFs, hq0nz, hsubM, hsubOne,
    Nat.mod_eq_of_lt hremM, Nat.mod_eq_of_lt hoffRawM,
    Nat.mod_eq_of_lt hq0M, Nat.mod_eq_of_lt h1M]

/-- On a window boundary the complete scalar prelude installs the first
prime-power cursor. -/
theorem p1224MarkPreludeBody_start_run (c : CellCfg) (k : Nat)
    (s : AState) (w : Nat) (hr : s.regs rR = 0)
    (hw : s.regs rW = w) (hT0 : 0 < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M) :
    let out := arun k s (p1224MarkPreludeBody c)
    out.regs 10 = 1 ∧ out.regs 11 = 1 ∧ out.regs 12 = 0 ∧
      out.regs 13 = 0 ∧ out.regs rPi = 0 ∧
      out.regs rQp = c.q0 ∧ out.regs rBp = c.q0 ∧
      out.regs rFs = 1 ∧
      out.regs rJ = p1224StartOffset w c.q0 ∧
      out.regs rR = 0 ∧ out.regs rW = w ∧ out.arr = s.arr := by
  let phased := arun k s (p1224MarkPhaseBody c)
  have hphase := p1224MarkPhaseBody_active_run c k s 0 hr hT0 hperiod
  dsimp only at hphase
  rcases hphase with ⟨h10, h11, h12, h13, harr0⟩
  have frame0 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkPhaseBody c) = false) :
      phased.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkPhaseBody c) h s
  have hr0 : phased.regs rR = 0 := (frame0 rR (by rfl)).trans hr
  have hw' : phased.regs rW = w := (frame0 rW (by rfl)).trans hw
  have hreset := p1224MarkResetBody_start_run c k phased w hr0 hw' hq0 hq0M
  dsimp only at hreset
  rcases hreset with ⟨hpi, hq, hbp, hfs, hj, harr1⟩
  let out := arun k phased (p1224MarkResetBody c)
  have frame1 (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        (p1224MarkResetBody c) = false) :
      out.regs r = phased.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r (p1224MarkResetBody c) h phased
  simp only [p1224MarkPreludeBody, arun_append]
  exact ⟨
    (frame1 10 (by rfl)).trans h10,
    (frame1 11 (by rfl)).trans h11,
    (frame1 12 (by rfl)).trans h12,
    (frame1 13 (by rfl)).trans h13,
    hpi, hq, hbp, hfs, hj,
    (frame1 rR (by rfl)).trans hr0,
    (frame1 rW (by rfl)).trans hw', harr1.trans harr0⟩

/-- On later marking rounds the scalar prelude preserves the complete cursor. -/
theorem p1224MarkPreludeBody_nonstart_run (c : CellCfg) (k : Nat)
    (s : AState) (r : Nat) (hr : s.regs rR = r) (hr0 : r ≠ 0)
    (hrT : r < c.markSteps)
    (hperiod : c.markSteps + c.segLen < M)
    (hq0 : 0 < c.q0) (hq0M : c.q0 < M)
    (hpiM : s.regs rPi < M) (hqM : s.regs rQp < M)
    (hbpM : s.regs rBp < M) (hfsM : s.regs rFs < M)
    (hjM : s.regs rJ < M) :
    let out := arun k s (p1224MarkPreludeBody c)
    out.regs 10 = 1 ∧ out.regs 11 = 1 ∧ out.regs 12 = 0 ∧
      out.regs 13 = 0 ∧ out.regs rPi = s.regs rPi ∧
      out.regs rQp = s.regs rQp ∧ out.regs rBp = s.regs rBp ∧
      out.regs rFs = s.regs rFs ∧ out.regs rJ = s.regs rJ ∧
      out.regs rR = r ∧ out.regs rW = s.regs rW ∧ out.arr = s.arr := by
  let phased := arun k s (p1224MarkPhaseBody c)
  have hphase := p1224MarkPhaseBody_active_run c k s r hr hrT hperiod
  dsimp only at hphase
  rcases hphase with ⟨h10, h11, h12, h13, harr0⟩
  have frame0 (x : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes x
        (p1224MarkPhaseBody c) = false) :
      phased.regs x = s.regs x :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k x (p1224MarkPhaseBody c) h s
  have hr' : phased.regs rR = r := (frame0 rR (by rfl)).trans hr
  have hreset := p1224MarkResetBody_nonstart_run c k phased r hr' hr0
    hq0 hq0M
    (by rw [frame0 rPi (by rfl)]; exact hpiM)
    (by rw [frame0 rQp (by rfl)]; exact hqM)
    (by rw [frame0 rBp (by rfl)]; exact hbpM)
    (by rw [frame0 rFs (by rfl)]; exact hfsM)
    (by rw [frame0 rJ (by rfl)]; exact hjM)
  dsimp only at hreset
  rcases hreset with ⟨hpi, hq, hbp, hfs, hj, harr1⟩
  let out := arun k phased (p1224MarkResetBody c)
  have frame1 (x : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes x
        (p1224MarkResetBody c) = false) :
      out.regs x = phased.regs x :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k x (p1224MarkResetBody c) h phased
  simp only [p1224MarkPreludeBody, arun_append]
  exact ⟨
    (frame1 10 (by rfl)).trans h10,
    (frame1 11 (by rfl)).trans h11,
    (frame1 12 (by rfl)).trans h12,
    (frame1 13 (by rfl)).trans h13,
    hpi.trans (frame0 rPi (by rfl)),
    hq.trans (frame0 rQp (by rfl)),
    hbp.trans (frame0 rBp (by rfl)),
    hfs.trans (frame0 rFs (by rfl)),
    hj.trans (frame0 rJ (by rfl)),
    (frame1 rR (by rfl)).trans hr',
    (frame1 rW (by rfl)).trans (frame0 rW (by rfl)),
    harr1.trans harr0⟩

theorem p1224MarkAddressBody_resident_run (c : CellCfg) (k : Nat)
    (s : AState) (j : Nat) (hj : s.regs rJ = j)
    (hactive : s.regs 10 = 1) (hjL : j < c.segLen)
    (haddr : j + 2 * c.segLen < M) :
    let out := arun k s (p1224MarkAddressBody c)
    out.regs 27 = 0 ∧ out.regs 30 = j ∧
      out.regs 31 = j + c.segLen ∧
      out.regs 32 = j + 2 * c.segLen ∧ out.arr = s.arr := by
  have hjM : j < M := by omega
  have hLM : c.segLen < M := by omega
  have h2LM : 2 * c.segLen < M := by omega
  have hjLM : j + c.segLen < M := by omega
  have h1M : (1 : Nat) < M := by decide
  have hj4 : s.regs 4 = j := by simpa [rJ] using hj
  have hsub : 1 + (M - 1) = M := by omega
  simp only [p1224MarkAddressBody, arun_lift]
  simp [p1224MarkAddressInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hj4, hactive, rJ, hjL, hsub,
    Nat.mod_eq_of_lt hjM, Nat.mod_eq_of_lt hLM,
    Nat.mod_eq_of_lt h2LM, Nat.mod_eq_of_lt hjLM,
    Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt h1M]

theorem p1224MarkAddressBody_past_run (c : CellCfg) (k : Nat)
    (s : AState) (j : Nat) (hj : s.regs rJ = j)
    (hactive : s.regs 10 = 1) (hjL : c.segLen ≤ j)
    (haddr : 6 * c.segLen < M) :
    let out := arun k s (p1224MarkAddressBody c)
    out.regs 27 = 1 ∧ out.regs 30 = 4 * c.segLen ∧
      out.regs 31 = 5 * c.segLen ∧
      out.regs 32 = 6 * c.segLen ∧ out.arr = s.arr := by
  have hLM : c.segLen < M := by omega
  have h2LM : 2 * c.segLen < M := by omega
  have h4LM : 4 * c.segLen < M := by omega
  have h5LM : 5 * c.segLen < M := by omega
  have h4add : 4 * c.segLen + c.segLen = 5 * c.segLen := by omega
  have h4add2 : 4 * c.segLen + 2 * c.segLen = 6 * c.segLen := by omega
  have h1M : (1 : Nat) < M := by decide
  have hj4 : s.regs 4 = j := by simpa [rJ] using hj
  simp only [p1224MarkAddressBody, arun_lift]
  simp [p1224MarkAddressInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hj4, hactive, rJ,
    show ¬j < c.segLen by omega, CellCfg.sink, h4add, h4add2,
    Nat.mod_eq_of_lt hLM, Nat.mod_eq_of_lt h2LM,
    Nat.mod_eq_of_lt h4LM, Nat.mod_eq_of_lt h5LM,
    Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt h1M]

#print axioms p1224MarkPhaseBody_active_run
#print axioms p1224MarkResetBody_nonstart_run
#print axioms p1224MarkResetBody_start_run
#print axioms p1224MarkPreludeBody_start_run
#print axioms p1224MarkPreludeBody_nonstart_run
#print axioms p1224MarkAddressBody_resident_run
#print axioms p1224MarkAddressBody_past_run

end LeanCompCert.Ports.Prop1224Cell

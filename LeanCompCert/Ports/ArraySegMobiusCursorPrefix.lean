import LeanCompCert.Ports.ArraySegMobiusCursorCore

/-!
# Cursor transitions of the full production marking prefix

Away from a window boundary, the twelve setup instructions must preserve the
persistent cursor before `markRound` executes.  This file verifies that fact
and lifts both cursor transitions to the actual `markPrefix` slice.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- Off a window boundary, production setup leaves the cursor unchanged. -/
theorem arun_markSetup_nonstart (c : Cfg) (idx : Nat) (s : AState)
    (hR : s.regs rR ≠ 0)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hpiM : s.regs rPi < M)
    (hpM : s.regs rP < M)
    (hjM : s.regs rJ < M) :
    let q := arun idx s (markSetup c)
    q.regs rPi = s.regs rPi ∧ q.regs rP = s.regs rP ∧
      q.regs rJ = s.regs rJ ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit ∧ q.regs 8 = s.regs 8 ∧
      q.arr = s.arr := by
  have hp1Ne : c.firstPrime ≠ 0 := Nat.ne_of_gt hp1Pos
  have hp1Mod : c.firstPrime % M = c.firstPrime := Nat.mod_eq_of_lt hp1M
  have hpiMod : s.regs rPi % M = s.regs rPi := Nat.mod_eq_of_lt hpiM
  have hpMod : s.regs rP % M = s.regs rP := Nat.mod_eq_of_lt hpM
  have hjMod : s.regs rJ % M = s.regs rJ := Nat.mod_eq_of_lt hjM
  have hpiMod2 : s.regs 2 % M = s.regs 2 := by simpa [rPi] using hpiMod
  have hpMod3 : s.regs 3 % M = s.regs 3 := by simpa [rP] using hpMod
  have hjMod4 : s.regs 4 % M = s.regs 4 := by simpa [rJ] using hjMod
  have hR5 : s.regs 5 ≠ 0 := by simpa [rR] using hR
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [markSetup, markPrefix, preSignal, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rR, rPi, rP, rJ, rW, rLimit, hR5, hp1Ne,
    hp1Mod, hpiMod2, hpMod3, hjMod4, h1mod]

/-- The full nonstart prefix keeps the current prime and advances its live
multiple by exactly that prime. -/
theorem arun_markPrefix_cursor_live_nonstart (c : Cfg) (idx : Nat)
    (s : AState) (pi p j w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = pi)
    (hp : s.regs rP = p)
    (hj : s.regs rJ = j)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hjL : j < c.segLen)
    (hpiLe : pi ≤ limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hnextM : j + p < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s (markPrefix c)
    out.regs rPi = pi ∧ out.regs rP = p ∧
      out.regs rJ = j + p ∧ out.regs rW = w ∧
      out.regs rLimit = limit := by
  let q := arun idx s (markSetup c)
  have hpiM : s.regs rPi < M := by rw [hpi]; omega
  have hpRegM : s.regs rP < M := by rw [hp]; exact hpM
  have hjM : s.regs rJ < M := by
    rw [hj]
    have hLM : c.segLen < M := by
      simp only [Cfg.arrayLen, Cfg.resultBase] at hA
      omega
    omega
  rcases arun_markSetup_nonstart c idx s hR hp1Pos hp1M hpiM hpRegM hjM with
    ⟨hqPi, hqP, hqJ, hqW, hqLimit, hqGate, _hqArr⟩
  change q.regs rPi = s.regs rPi at hqPi
  change q.regs rP = s.regs rP at hqP
  change q.regs rJ = s.regs rJ at hqJ
  change q.regs rW = s.regs rW at hqW
  change q.regs rLimit = s.regs rLimit at hqLimit
  change q.regs 8 = s.regs 8 at hqGate
  rcases arun_markRound_cursor_live c idx q pi p j w limit
      (hqGate.trans hgate) (hqPi.trans hpi) (hqP.trans hp)
      (hqJ.trans hj) (hqW.trans hw) (hqLimit.trans hlimit)
      hjL hpiLe hlimitLe hlimitM hpPos hpM hnextM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩
  rw [markPrefix_eq_setup_round, arun_append]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

/-- The full nonstart prefix advances an exhausted prime to the following
table entry and selects its first multiple or the terminal sentinel. -/
theorem arun_markPrefix_cursor_advance_nonstart (c : Cfg) (idx : Nat)
    (s : AState) (pi p w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = pi)
    (hj : c.segLen ≤ s.regs rJ)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hpiLt : pi < limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hcurPM : s.regs rP < M)
    (hjM : s.regs rJ < M)
    (htable : s.arr (c.primeBase + (pi + 1)) = p)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s (markPrefix c)
    out.regs rPi = pi + 1 ∧ out.regs rP = p ∧
      out.regs rJ = (if pi + 1 = limit then c.segLen + 1
        else firstOffset w p) ∧
      out.regs rW = w ∧ out.regs rLimit = limit := by
  let q := arun idx s (markSetup c)
  have hpiM : s.regs rPi < M := by rw [hpi]; omega
  rcases arun_markSetup_nonstart c idx s hR hp1Pos hp1M hpiM hcurPM hjM with
    ⟨hqPi, _hqP, hqJ, hqW, hqLimit, hqGate, hqArr⟩
  change q.regs rPi = s.regs rPi at hqPi
  change q.regs rJ = s.regs rJ at hqJ
  change q.regs rW = s.regs rW at hqW
  change q.regs rLimit = s.regs rLimit at hqLimit
  change q.regs 8 = s.regs 8 at hqGate
  change q.arr = s.arr at hqArr
  have htableQ : q.arr (c.primeBase + (pi + 1)) = p := by
    rw [congrFun hqArr, htable]
  rcases arun_markRound_cursor_advance c idx q pi p w limit
      (hqGate.trans hgate) (hqPi.trans hpi)
      (by rw [hqJ]; exact hj) (hqW.trans hw) (hqLimit.trans hlimit)
      hpiLt hlimitLe hlimitM htableQ hpPos hpM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩
  rw [markPrefix_eq_setup_round, arun_append]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

/-- At a window boundary, the full prefix resets to the first prime, marks
its first multiple, and leaves the cursor ready at the following multiple. -/
theorem arun_markPrefix_cursor_live_start (c : Cfg) (idx : Nat)
    (s : AState) (w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hR : s.regs rR = 0)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hpPos : 0 < c.firstPrime)
    (hpLeL : c.firstPrime ≤ c.segLen)
    (hpM : c.firstPrime < M)
    (hA : c.arrayLen < M) :
    let j := firstOffset w c.firstPrime
    let out := arun idx s (markPrefix c)
    out.regs rPi = 0 ∧ out.regs rP = c.firstPrime ∧
      out.regs rJ = j + c.firstPrime ∧ out.regs rW = w ∧
      out.regs rLimit = limit := by
  let j := firstOffset w c.firstPrime
  let q := arun idx s (markSetup c)
  rcases arun_markSetup_start c idx s hR hpPos hpM with
    ⟨hqPi, hqP, hqJ, hqW, hqGate⟩
  change q.regs rPi = 0 at hqPi
  change q.regs rP = c.firstPrime at hqP
  change q.regs rJ = firstOffset (s.regs rW) c.firstPrime at hqJ
  change q.regs rW = s.regs rW at hqW
  change q.regs 8 = s.regs 8 at hqGate
  have hqJ' : q.regs rJ = j := by rw [hqJ, hw]
  have hqW' : q.regs rW = w := hqW.trans hw
  have hqLimit : q.regs rLimit = limit := by
    rw [arun_reg_frame idx rLimit (markSetup c) s (by rfl), hlimit]
  have hjL : j < c.segLen := by
    have hjp : j < c.firstPrime := Nat.mod_lt _ hpPos
    omega
  have hnextM : j + c.firstPrime < M := by
    have hjp : j < c.firstPrime := Nat.mod_lt _ hpPos
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  rcases arun_markRound_cursor_live c idx q 0 c.firstPrime j w limit
      (hqGate.trans hgate) hqPi hqP hqJ' hqW' hqLimit hjL
      (Nat.zero_le _) hlimitLe hlimitM hpPos hpM hnextM hA with
    ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩
  rw [markPrefix_eq_setup_round, arun_append]
  exact ⟨hoPi, hoP, hoJ, hoW, hoLimit⟩

end LeanCompCert.Ports.ArraySegMobiusMark

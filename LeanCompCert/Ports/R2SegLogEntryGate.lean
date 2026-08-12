import LeanCompCert.Ports.R2SegLogRoundStep

/-!
# Stream load and live-entry gate for the `R₂*` log phase

The first nine instructions of `R2Cfg.logBody` address the current two-word
stream cell, load it, and form the live/start gates.  This leaf gives their
exact semantics under the ordinary stream cursor and address bounds.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def logEntryGateBody (c : R2Cfg) : List AInstr := c.logBody.take 9

theorem logEntryGateBody_eq_slice (c : R2Cfg) :
    c.logBody.take 9 = logEntryGateBody c := by
  rfl

/-- A readable stream cell in the active log phase is loaded exactly.  The
start gate is one precisely when the persistent round counter is zero. -/
theorem logEntryGateBody_live_run (c : R2Cfg) (k : Nat) (s : AState)
    (ec wc j : Nat)
    (hec : s.regs rEc = ec) (hwc : s.regs rWc = wc)
    (hk : s.regs rK = j) (hphase : s.regs 15 = 1)
    (hlive : ec < wc) (hbase : c.streamBase < M)
    (haddr : (ec <<< 1) + c.streamBase + 1 < M) :
    let addr := (ec <<< 1) + c.streamBase
    let out := arun k s (logEntryGateBody c)
    out.regs 202 = s.arr addr ∧ out.regs 204 = s.arr (addr + 1) ∧
      out.regs 205 = 1 ∧ out.regs 206 = 1 ∧
      out.regs 208 = (if j = 0 then 1 else 0) ∧ out.arr = s.arr := by
  have hshift : ec <<< 1 < M := by omega
  have haddr0 : (ec <<< 1) + c.streamBase < M := by omega
  have hbaseMod : c.streamBase % M = c.streamBase := Nat.mod_eq_of_lt hbase
  have h1 : (1 : Nat) % M = 1 := by decide
  have hec' : s.regs 192 = ec := by simpa only [rEc] using hec
  have hwc' : s.regs 191 = wc := by simpa only [rWc] using hwc
  have hk' : s.regs 193 = j := by simpa only [rK] using hk
  by_cases hj : j = 0
  · simp [logEntryGateBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      hec', hwc', hk', hphase, hlive, hj, hbaseMod, h1,
      Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt haddr0,
      Nat.mod_eq_of_lt haddr, rEc, rWc, rK]
  · simp [logEntryGateBody, R2Cfg.logBody, arun, astep,
      AState.writeReg, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      hec', hwc', hk', hphase, hlive, hj, hbaseMod, h1,
      Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt haddr0,
      Nat.mod_eq_of_lt haddr, rEc, rWc, rK]

#print axioms logEntryGateBody_eq_slice
#print axioms logEntryGateBody_live_run

end LeanCompCert.Ports.R2SegSieve

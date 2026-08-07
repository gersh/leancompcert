import LeanCompCert.Ports.ArraySegMobiusCursorStep

/-!
# Cursor input produced by the real marking stores

The range gate (`rJ < segLen`) is computed before the product and flag stores.
This file proves that those stores and their intervening arithmetic preserve
the persistent cursor registers and carry the exact range bit to the verified
post-store cursor transition.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- The two instructions that compute `inR`. -/
def roundRangeGate (c : Cfg) : List AInstr := (roundBeforeProd c).take 2

/-- The remaining address/product arithmetic before the product store. -/
def roundBeforeProdRest (c : Cfg) : List AInstr := (roundBeforeProd c).drop 2

/-- Everything in a reset-independent mark up to and including the flag
store, i.e. the input state of `roundAfterFlag`. -/
def roundCursorInput (c : Cfg) : List AInstr := (markRound c).take 21

theorem roundBeforeProd_eq_rangeSlices (c : Cfg) :
    roundBeforeProd c = roundRangeGate c ++ roundBeforeProdRest c := by
  rfl

theorem markRound_eq_cursorInput_after (c : Cfg) :
    markRound c = roundCursorInput c ++ roundAfterFlag c := by
  rfl

/-- A target inside the current window produces `inR = 1`. -/
theorem roundRangeGate_live (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hj : s.regs rJ < c.segLen)
    (hLM : c.segLen < M) :
    (arun idx s (roundRangeGate c)).regs 21 = 1 := by
  have hLmod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hLM
  have hj4 : s.regs 4 < c.segLen := by simpa [rJ] using hj
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [roundRangeGate, roundBeforeProd, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rJ, hgate, hj4, hLmod, h1mod]

/-- A target at or beyond the end of the window produces `inR = 0`. -/
theorem roundRangeGate_exhausted (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hj : c.segLen ≤ s.regs rJ)
    (hLM : c.segLen < M) :
    (arun idx s (roundRangeGate c)).regs 21 = 0 := by
  have hLmod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hLM
  have hj4 : c.segLen ≤ s.regs 4 := by simpa [rJ] using hj
  have hnot4 : ¬s.regs 4 < c.segLen := by omega
  simp [roundRangeGate, roundBeforeProd, markRound, markPrefix, preSignal,
    Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rJ, hgate, hnot4, hLmod]

/-- The actual product/flag prefix carries the live range bit and every
persistent cursor register to `roundAfterFlag`. -/
theorem roundCursorInput_live (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hj : s.regs rJ < c.segLen)
    (hLM : c.segLen < M) :
    let q := arun idx s (roundCursorInput c)
    q.regs 21 = 1 ∧ q.regs 8 = 1 ∧
      q.regs rPi = s.regs rPi ∧ q.regs rP = s.regs rP ∧
      q.regs rJ = s.regs rJ ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit := by
  let g := arun idx s (roundRangeGate c)
  have hg : g.regs 21 = 1 := roundRangeGate_live c idx s hgate hj hLM
  have hdecomp : arun idx s (roundCursorInput c) =
      arun idx g (roundBeforeProdRest c ++ [.store 25 30] ++
        markBetweenStores c ++ [.store 26 38]) := by
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdecomp]
    exact arun_reg_frame idx 21
      (roundBeforeProdRest c ++ [.store 25 30] ++
        markBetweenStores c ++ [.store 26 38]) g (by rfl) |>.trans hg
  · exact arun_reg_frame idx 8 (roundCursorInput c) s (by rfl) |>.trans hgate
  · exact arun_reg_frame idx rPi (roundCursorInput c) s (by rfl)
  · exact arun_reg_frame idx rP (roundCursorInput c) s (by rfl)
  · exact arun_reg_frame idx rJ (roundCursorInput c) s (by rfl)
  · exact arun_reg_frame idx rW (roundCursorInput c) s (by rfl)
  · exact arun_reg_frame idx rLimit (roundCursorInput c) s (by rfl)

/-- The same real prefix carries the exhausted range bit and cursor registers
to the transition block. -/
theorem roundCursorInput_exhausted (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hj : c.segLen ≤ s.regs rJ)
    (hLM : c.segLen < M) :
    let q := arun idx s (roundCursorInput c)
    q.regs 21 = 0 ∧ q.regs 8 = 1 ∧
      q.regs rPi = s.regs rPi ∧ q.regs rP = s.regs rP ∧
      q.regs rJ = s.regs rJ ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit := by
  let g := arun idx s (roundRangeGate c)
  have hg : g.regs 21 = 0 := roundRangeGate_exhausted c idx s hgate hj hLM
  have hdecomp : arun idx s (roundCursorInput c) =
      arun idx g (roundBeforeProdRest c ++ [.store 25 30] ++
        markBetweenStores c ++ [.store 26 38]) := by
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdecomp]
    exact arun_reg_frame idx 21
      (roundBeforeProdRest c ++ [.store 25 30] ++
        markBetweenStores c ++ [.store 26 38]) g (by rfl) |>.trans hg
  · exact arun_reg_frame idx 8 (roundCursorInput c) s (by rfl) |>.trans hgate
  · exact arun_reg_frame idx rPi (roundCursorInput c) s (by rfl)
  · exact arun_reg_frame idx rP (roundCursorInput c) s (by rfl)
  · exact arun_reg_frame idx rJ (roundCursorInput c) s (by rfl)
  · exact arun_reg_frame idx rW (roundCursorInput c) s (by rfl)
  · exact arun_reg_frame idx rLimit (roundCursorInput c) s (by rfl)

/-- An exhausted prime writes only to the two dedicated mark sinks. -/
theorem roundBeforeProd_exhausted_addresses (c : Cfg) (idx : Nat)
    (s : AState)
    (hgate : s.regs 8 = 1)
    (hj : c.segLen ≤ s.regs rJ)
    (hA : c.arrayLen < M) :
    let q := arun idx s (roundBeforeProd c)
    q.regs 25 = c.sinkProd ∧
      q.regs 26 = c.sinkProd + c.segLen := by
  have hL : c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  have h2L : c.sinkProd < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase, Cfg.sinkProd] at hA ⊢
    omega
  have h3L : c.sinkProd + c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase, Cfg.sinkProd] at hA ⊢
    omega
  have hLM : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hL
  have h2LM : c.sinkProd % M = c.sinkProd := Nat.mod_eq_of_lt h2L
  have h3LM : (c.sinkProd + c.segLen) % M = c.sinkProd + c.segLen :=
    Nat.mod_eq_of_lt h3L
  have hj4 : c.segLen ≤ s.regs 4 := by simpa [rJ] using hj
  have hnot4 : ¬s.regs 4 < c.segLen := by omega
  set_option maxRecDepth 10000 in
    simp [roundBeforeProd, markRound, markPrefix, preSignal, Cfg.coreBody,
      arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rPi, rP, rJ, rW, rLimit, hgate, hnot4,
      hLM, h2LM, h3LM]

/-- Apart from the two dedicated sinks, an exhausted marking prefix preserves
every array cell, in particular every prime-table cell. -/
theorem roundCursorInput_exhausted_cell (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hj : c.segLen ≤ s.regs rJ)
    (hA : c.arrayLen < M)
    (x : Nat)
    (hprod : x ≠ c.sinkProd)
    (hflag : x ≠ c.sinkProd + c.segLen) :
    (arun idx s (roundCursorInput c)).arr x = s.arr x := by
  let s0 := arun idx s (roundBeforeProd c)
  let s1 := astep idx s0 (.store 25 30)
  let s2 := arun idx s1 (markBetweenStores c)
  let s3 := astep idx s2 (.store 26 38)
  have ha := roundBeforeProd_exhausted_addresses c idx s hgate hj hA
  have h25 : s0.regs 25 = c.sinkProd := ha.1
  have h26 : s0.regs 26 = c.sinkProd + c.segLen := ha.2
  have hs0arr : s0.arr = s.arr :=
    arun_arr_frame idx (roundBeforeProd c) s (by rfl)
  have hs2arr : s2.arr = s1.arr :=
    arun_arr_frame idx (markBetweenStores c) s1 (by rfl)
  have hs2r26 : s2.regs 26 = c.sinkProd + c.segLen := by
    rw [arun_reg_frame idx 26 (markBetweenStores c) s1 (by rfl)]
    exact h26
  have hdecomp : arun idx s (roundCursorInput c) = s3 := by
    rfl
  rw [hdecomp]
  change (s2.writeArr (s2.regs 26) (s2.regs 38)).arr x = s.arr x
  rw [AState.writeArr_arr_ne s2 _ (by rw [hs2r26]; exact hflag)]
  rw [congrFun hs2arr]
  change (s0.writeArr (s0.regs 25) (s0.regs 30)).arr x = s.arr x
  rw [AState.writeArr_arr_ne s0 _ (by rw [h25]; exact hprod)]
  exact congrFun hs0arr x

end LeanCompCert.Ports.ArraySegMobiusMark

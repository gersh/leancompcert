import LeanCompCert.Ports.ArraySegMobiusSignal

/-!
# Marking-step refinement for the production segmented Möbius sieve

`ArraySegMobiusSignal` reduces the production decoder to a loop-entry
`CellRepresents` invariant.  This file starts the preceding induction.  It
extracts the exact product/parity update made by one live marking round,
without unfolding the complete 111-instruction core in one simplifier call.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- Exact word-level product-cell update for one distinct prime hit. -/
def prodUpdate (prod p : Nat) : Nat :=
  ((prod + if prod = 0 then 1 else 0) * p) % M

/-- Exact word-level parity/square-hit update for one prime hit. -/
def flagUpdate (n flag p : Nat) : Nat :=
  let squareHit := if n % (p * p) = 0 then 2 else 0
  (((flag ^^^ 1) % M) ||| squareHit) % M

/-- Four scalar instructions computing the two clear-store addresses. -/
def postBeforeClear (c : Cfg) : List AInstr :=
  [ .scalar (.binop 82 .sub (.lit 1) (.reg 9))
  , .scalar (.binop 83 .mul (.reg 82) (.lit c.sinkProd))
  , .scalar (.binop 84 .add (.reg 63) (.reg 83))
  , .scalar (.binop 85 .add (.reg 84) (.lit c.segLen)) ]

/-- The four-instruction root-collection gate. -/
def postRootBeforeCollect (c : Cfg) : List AInstr :=
  [ .scalar (.binop 134 .sub (.reg 65) (.lit 2))
  , .scalar (.binop 135 .lt (.reg 134) (.lit (c.rootCap - 1)))
  , .scalar (.binop 136 .mul (.reg 135) (.reg 67)) ]

/-- The four-instruction root-collection gate. -/
def postRootGate (c : Cfg) : List AInstr :=
  postRootBeforeCollect c ++
    [.scalar (.binop 137 .mul (.reg 136) (.reg 132))]

/-- The four-instruction selection of the live or sink root-store address. -/
def postRootAddress (c : Cfg) : List AInstr :=
  [ .scalar (.binop 138 .mul (.reg 137) (.reg rWrite))
  , .scalar (.binop 139 .sub (.lit 1) (.reg 137))
  , .scalar (.binop 140 .mul (.reg 139) (.lit c.primeSink))
  , .scalar (.binop 141 .add (.reg 138) (.reg 140)) ]

/-- Eight scalar instructions computing the root-table store address. -/
def postBeforeRootStore (c : Cfg) : List AInstr :=
  postRootGate c ++ postRootAddress c

/-- Store-free cursor/window update after the root-table store. -/
def postAfterRootStore (c : Cfg) : List AInstr :=
  [ .scalar (.binop rWrite .add (.reg rWrite) (.reg 137))
  , .scalar (.binop 86 .add (.reg rR) (.lit 1))
  , .scalar (.binop 87 .eq (.reg 86) (.lit c.period))
  , .scalar (.binop 88 .sub (.lit 1) (.reg 87))
  , .scalar (.binop rR .mul (.reg 88) (.reg 86))
  , .scalar (.binop 89 .mul (.reg 87) (.lit c.segLen))
  , .scalar (.binop 142 .eq .idx (.lit (c.rootSpan - 1)))
  , .scalar (.binop 143 .mul (.reg 142) (.lit c.wDelta))
  , .scalar (.binop 144 .add (.reg 89) (.reg 143))
  , .scalar (.binop rW .add (.reg rW) (.reg 144)) ]

theorem postSignal_eq_storeSlices (c : Cfg) :
    postSignal c = postBeforeClear c ++ [.store 84 rZero] ++
      [.store 85 rZero] ++ postBeforeRootStore c ++ [.store 141 65] ++
      postAfterRootStore c := by
  rfl

theorem postBeforeRootStore_eq_slices (c : Cfg) :
    postBeforeRootStore c = postRootGate c ++ postRootAddress c := by
  rfl

theorem postRootGate_eq_slices (c : Cfg) :
    postRootGate c = postRootBeforeCollect c ++
      [.scalar (.binop 137 .mul (.reg 136) (.reg 132))] := by
  rfl

/-- A loop position in the marking phase sets the production mark gate. -/
theorem selectorBlock_markGate (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hTM : c.markSteps < M) :
    (arun idx s (selectorBlock c)).regs 8 = 1 := by
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hmark5 : s.regs 5 < c.markSteps := by simpa [rR] using hmark
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rR, rLimit, hTmod, hmark5]

/-- Away from the window-start reset, a live mark computes the real product
and flag addresses and the exact product value to be stored.  This is the
store-free first slice of the production body, not a reimplementation. -/
theorem markBeforeProd_live_nonstart (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hR : s.regs rR ≠ 0)
    (hj : s.regs rJ < c.segLen)
    (hpM : s.regs rP < M)
    (hA : c.arrayLen < M) :
    let q := arun idx s (markBeforeProd c)
    q.regs 25 = s.regs rJ ∧
      q.regs 26 = s.regs rJ + c.segLen ∧
      q.regs 30 = prodUpdate (s.arr (s.regs rJ)) (s.regs rP) ∧
      q.regs rP = s.regs rP ∧ q.regs rW = s.regs rW := by
  have hL : c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  have hjM : s.regs rJ < M := by omega
  have hjLM : s.regs rJ + c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  have hLM : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hL
  have hjmod : s.regs rJ % M = s.regs rJ := Nat.mod_eq_of_lt hjM
  have hjLmod : (s.regs rJ + c.segLen) % M =
      s.regs rJ + c.segLen := Nat.mod_eq_of_lt hjLM
  have hR5 : s.regs 5 ≠ 0 := by simpa [rR] using hR
  have hj4 : s.regs 4 < c.segLen := by simpa [rJ] using hj
  have hjmod4 : s.regs 4 % M = s.regs 4 := by simpa [rJ] using hjmod
  have hjLmod4 : (s.regs 4 + c.segLen) % M =
      s.regs 4 + c.segLen := by simpa [rJ] using hjLmod
  have hp3mod : s.regs 3 % M = s.regs 3 := by
    apply Nat.mod_eq_of_lt
    simpa [rP] using hpM
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hOne : 1 + (M - 1) = M := by
    have := M_pos
    omega
  set_option maxRecDepth 10000 in
    simp [markBeforeProd, markPrefix, preSignal, Cfg.coreBody, prodUpdate,
      arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rR, rW, rP, rJ, rPi, rLimit,
      hgate, hR5, hj4, hLM, hjmod4, hjLmod4, hp3mod, h1mod, hOne]
    rfl

/-- The eight instructions between the two stores compute the exact
parity/square-hit flag from their named address, prime, and window base. -/
theorem markBetweenStores_live (c : Cfg) (idx : Nat) (s : AState)
    (j p w : Nat)
    (h25 : s.regs 25 = j)
    (h26 : s.regs 26 = j + c.segLen)
    (hp : s.regs rP = p)
    (hw : s.regs rW = w)
    (hnM : w + j < M)
    (hpPos : 0 < p)
    (hpSqM : p * p < M) :
    (arun idx s (markBetweenStores c)).regs 38 =
      flagUpdate (w + j) (s.arr (j + c.segLen)) p := by
  have hpSqPositive : 0 < p * p := Nat.mul_pos hpPos hpPos
  have hpSqPos : p * p ≠ 0 := Nat.ne_of_gt hpSqPositive
  have hpSqMod : (p * p) % M = p * p := Nat.mod_eq_of_lt hpSqM
  have hnMod : (j + w) % M = w + j := by
    rw [Nat.add_comm, Nat.mod_eq_of_lt hnM]
  have hp3 : s.regs 3 = p := by simpa [rP] using hp
  have hw6 : s.regs 6 = w := by simpa [rW] using hw
  have hremM : (w + j) % (p * p) % M = (w + j) % (p * p) := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hpSqPositive) (Nat.le_of_lt hpSqM)
  have h1mod : (1 : Nat) % M = 1 := by decide
  have h2mod : (2 : Nat) % M = 2 := by decide
  set_option maxRecDepth 10000 in
    simp [markBetweenStores, markPrefix, preSignal, Cfg.coreBody,
      flagUpdate, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rP, rW, h25, h26, hp3, hw6, hnMod, hpSqMod,
      hpSqPos, hremM, h1mod, h2mod]
    by_cases hhit : (w + j) % (p * p) = 0 <;> simp [hhit, h2mod]

/-- Exact array effect of one ordinary live marking round.  The two touched
cells receive the pure product/parity updates and every other cell is framed.
The window-start reset is intentionally a separate induction base. -/
theorem arun_markPrefix_live_nonstart (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hR : s.regs rR ≠ 0)
    (hj : s.regs rJ < c.segLen)
    (hpPos : 0 < s.regs rP)
    (hpM : s.regs rP < M)
    (hpSqM : s.regs rP * s.regs rP < M)
    (hnM : s.regs rW + s.regs rJ < M)
    (hA : c.arrayLen < M) :
    let j := s.regs rJ
    let p := s.regs rP
    let w := s.regs rW
    let out := arun idx s (markPrefix c)
    out.arr j = prodUpdate (s.arr j) p ∧
      out.arr (j + c.segLen) = flagUpdate (w + j) (s.arr (j + c.segLen)) p ∧
      ∀ x, x ≠ j → x ≠ j + c.segLen → out.arr x = s.arr x := by
  let j := s.regs rJ
  let p := s.regs rP
  let w := s.regs rW
  let s0 := arun idx s (markBeforeProd c)
  let s1 := astep idx s0 (.store 25 30)
  let s2 := arun idx s1 (markBetweenStores c)
  let s3 := astep idx s2 (.store 26 38)
  have hb := markBeforeProd_live_nonstart c idx s hgate hR hj hpM hA
  have hjp : j < c.segLen := by exact hj
  have hLpos : 0 < c.segLen := by omega
  have hne : j ≠ j + c.segLen := by omega
  have hs0arr : s0.arr = s.arr :=
    arun_arr_frame idx (markBeforeProd c) s (by rfl)
  have hs0r25 : s0.regs 25 = j := by exact hb.1
  have hs0r26 : s0.regs 26 = j + c.segLen := by exact hb.2.1
  have hs0r30 : s0.regs 30 = prodUpdate (s.arr j) p := by exact hb.2.2.1
  have hs0rp : s0.regs rP = p := by exact hb.2.2.2.1
  have hs0rw : s0.regs rW = w := by exact hb.2.2.2.2
  have hs1r25 : s1.regs 25 = j := hs0r25
  have hs1r26 : s1.regs 26 = j + c.segLen := hs0r26
  have hs1rp : s1.regs rP = p := hs0rp
  have hs1rw : s1.regs rW = w := hs0rw
  have hs1prod : s1.arr j = prodUpdate (s.arr j) p := by
    change (s0.writeArr (s0.regs 25) (s0.regs 30)).arr j = _
    rw [hs0r25, AState.writeArr_arr_self, hs0r30]
  have hs1flag : s1.arr (j + c.segLen) = s.arr (j + c.segLen) := by
    have hnot : j + c.segLen ≠ s0.regs 25 := by
      rw [hs0r25]
      exact Ne.symm hne
    change (s0.writeArr (s0.regs 25) (s0.regs 30)).arr
      (j + c.segLen) = _
    rw [AState.writeArr_arr_ne s0 _ hnot, congrFun hs0arr]
  have hs2arr : s2.arr = s1.arr :=
    arun_arr_frame idx (markBetweenStores c) s1 (by rfl)
  have hs2r26 : s2.regs 26 = j + c.segLen := by
    rw [arun_reg_frame idx 26 (markBetweenStores c) s1 (by rfl)]
    exact hs1r26
  have hs2flag : s2.regs 38 = flagUpdate (w + j) (s.arr (j + c.segLen)) p := by
    rw [markBetweenStores_live c idx s1 j p w hs1r25 hs1r26 hs1rp hs1rw
      hnM hpPos hpSqM, hs1flag]
  have hdecomp : arun idx s (markPrefix c) =
      arun idx s3 (markAfterFlag c) := by
    rw [markPrefix_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append]
    rfl
  have hfinal (x : Nat) :
      (arun idx s (markPrefix c)).arr x = s3.arr x := by
    rw [hdecomp]
    exact congrFun (arun_arr_frame idx (markAfterFlag c) s3 (by rfl)) x
  refine ⟨?_, ?_, ?_⟩
  · rw [hfinal]
    change s3.arr j = _
    have hnot : j ≠ s2.regs 26 := by rw [hs2r26]; exact hne
    change (s2.writeArr (s2.regs 26) (s2.regs 38)).arr j = _
    rw [AState.writeArr_arr_ne s2 _ hnot]
    rw [congrFun hs2arr j]
    simpa [j, p] using hs1prod
  · rw [hfinal]
    change s3.arr (j + c.segLen) = _
    change (s2.writeArr (s2.regs 26) (s2.regs 38)).arr
      (j + c.segLen) = _
    rw [hs2r26, AState.writeArr_arr_self, hs2flag]
  · intro x hxj hxflag
    rw [hfinal]
    change s3.arr x = s.arr x
    have hnotFlag : x ≠ s2.regs 26 := by
      rw [hs2r26]
      exact hxflag
    change (s2.writeArr (s2.regs 26) (s2.regs 38)).arr x = s.arr x
    rw [AState.writeArr_arr_ne s2 _ hnotFlag]
    rw [congrFun hs2arr x]
    change s1.arr x = s.arr x
    have hnotProd : x ≠ s0.regs 25 := by
      rw [hs0r25]
      exact hxj
    change (s0.writeArr (s0.regs 25) (s0.regs 30)).arr x = s.arr x
    rw [AState.writeArr_arr_ne s0 _ hnotProd]
    exact congrFun hs0arr x

/-- Loop-entry form of one ordinary live marking round.  The selector is
discharged from `rR < markSteps`; all product/flag updates are stated against
the input array and persistent cursor registers. -/
theorem signalInput_mark_live_nonstart (c : Cfg) (idx : Nat) (s : AState)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hj : s.regs rJ < c.segLen)
    (hpPos : 0 < s.regs rP)
    (hpM : s.regs rP < M)
    (hpSqM : s.regs rP * s.regs rP < M)
    (hnM : s.regs rW + s.regs rJ < M)
    (hTM : c.markSteps < M)
    (hA : c.arrayLen < M) :
    let j := s.regs rJ
    let p := s.regs rP
    let w := s.regs rW
    let out := signalInput c idx s
    out.arr j = prodUpdate (s.arr j) p ∧
      out.arr (j + c.segLen) = flagUpdate (w + j) (s.arr (j + c.segLen)) p ∧
      ∀ x, x ≠ j → x ≠ j + c.segLen → out.arr x = s.arr x := by
  let q := arun idx s (selectorBlock c)
  have hgate : q.regs 8 = 1 := selectorBlock_markGate c idx s hmark hTM
  have hqR : q.regs rR = s.regs rR :=
    arun_reg_frame idx rR (selectorBlock c) s (by rfl)
  have hqJ : q.regs rJ = s.regs rJ :=
    arun_reg_frame idx rJ (selectorBlock c) s (by rfl)
  have hqP : q.regs rP = s.regs rP :=
    arun_reg_frame idx rP (selectorBlock c) s (by rfl)
  have hqW : q.regs rW = s.regs rW :=
    arun_reg_frame idx rW (selectorBlock c) s (by rfl)
  have hqarr : q.arr = s.arr :=
    arun_arr_frame idx (selectorBlock c) s (by rfl)
  have hm := arun_markPrefix_live_nonstart c idx q hgate
    (by rw [hqR]; exact hR)
    (by rw [hqJ]; exact hj)
    (by rw [hqP]; exact hpPos)
    (by rw [hqP]; exact hpM)
    (by rw [hqP]; exact hpSqM)
    (by rw [hqW, hqJ]; exact hnM) hA
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  refine ⟨?_, ?_, ?_⟩
  · change (arun idx q (markPrefix c)).arr (s.regs rJ) = _
    calc
      _ = (arun idx q (markPrefix c)).arr (q.regs rJ) := by rw [hqJ]
      _ = prodUpdate (q.arr (q.regs rJ)) (q.regs rP) := hm.1
      _ = prodUpdate (s.arr (s.regs rJ)) (s.regs rP) := by
        rw [hqJ, hqP, congrFun hqarr]
  · change (arun idx q (markPrefix c)).arr
      (s.regs rJ + c.segLen) = _
    calc
      _ = (arun idx q (markPrefix c)).arr
          (q.regs rJ + c.segLen) := by rw [hqJ]
      _ = flagUpdate (q.regs rW + q.regs rJ)
          (q.arr (q.regs rJ + c.segLen)) (q.regs rP) := hm.2.1
      _ = flagUpdate (s.regs rW + s.regs rJ)
          (s.arr (s.regs rJ + c.segLen)) (s.regs rP) := by
        rw [hqJ, hqP, hqW, congrFun hqarr]
  · intro x hxj hxflag
    change (arun idx q (markPrefix c)).arr x = s.arr x
    calc
      _ = q.arr x := hm.2.2 x (by rw [hqJ]; exact hxj)
        (by rw [hqJ]; exact hxflag)
      _ = s.arr x := congrFun hqarr x

end LeanCompCert.Ports.ArraySegMobiusMark

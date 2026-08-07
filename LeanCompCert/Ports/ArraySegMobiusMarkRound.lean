import LeanCompCert.Ports.ArraySegMobiusMarkCore

/-!
# Reset-independent production marking round

The first twelve instructions of `markPrefix` only select the prime cursor at
a window boundary.  This file removes that setup from the two live stores, so
the same exact cell-update theorem can be used by both the ordinary and
window-start induction cases.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- Window-start cursor selection, before the actual mark. -/
def markSetup (c : Cfg) : List AInstr := (markPrefix c).take 12

/-- The actual mark and cursor advance, after window-start selection. -/
def markRound (c : Cfg) : List AInstr := (markPrefix c).drop 12

/-- Store-free address/product calculation of a reset-independent round. -/
def roundBeforeProd (c : Cfg) : List AInstr := (markRound c).take 11

/-- Store-free cursor advance after the flag store. -/
def roundAfterFlag (c : Cfg) : List AInstr := (markRound c).drop 21

theorem markPrefix_eq_setup_round (c : Cfg) :
    markPrefix c = markSetup c ++ markRound c := by
  rfl

theorem markRound_eq_storeSlices (c : Cfg) :
    markRound c = roundBeforeProd c ++ [.store 25 30] ++
      markBetweenStores c ++ [.store 26 38] ++ roundAfterFlag c := by
  rfl

/-- First multiple of `p` in the window whose base is `w`. -/
def firstOffset (w p : Nat) : Nat := (p - w % p) % p

/-- At a window start the production setup selects table entry zero, the
bootstrap first prime, and its first multiple in the new window. -/
theorem arun_markSetup_start (c : Cfg) (idx : Nat) (s : AState)
    (hR : s.regs rR = 0)
    (hpPos : 0 < c.firstPrime)
    (hpM : c.firstPrime < M) :
    let q := arun idx s (markSetup c)
    q.regs rPi = 0 ∧ q.regs rP = c.firstPrime ∧
      q.regs rJ = firstOffset (s.regs rW) c.firstPrime ∧
      q.regs rW = s.regs rW ∧ q.regs 8 = s.regs 8 := by
  have hpmod : c.firstPrime % M = c.firstPrime := Nat.mod_eq_of_lt hpM
  have hpNe : c.firstPrime ≠ 0 := Nat.ne_of_gt hpPos
  have hremLt : s.regs rW % c.firstPrime < c.firstPrime :=
    Nat.mod_lt _ hpPos
  have hremM : (s.regs rW % c.firstPrime) % M =
      s.regs rW % c.firstPrime := Nat.mod_eq_of_lt (by omega)
  have hsubRaw :
      (c.firstPrime + (M - s.regs rW % c.firstPrime)) % M =
        c.firstPrime - s.regs rW % c.firstPrime := by
    have hsplit :
        c.firstPrime + (M - s.regs rW % c.firstPrime) =
          M + (c.firstPrime - s.regs rW % c.firstPrime) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hoffM :
      ((c.firstPrime - s.regs rW % c.firstPrime) % c.firstPrime) % M =
        (c.firstPrime - s.regs rW % c.firstPrime) % c.firstPrime := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hpPos) (Nat.le_of_lt hpM)
  have hremM6 : (s.regs 6 % c.firstPrime) % M =
      s.regs 6 % c.firstPrime := by simpa [rW] using hremM
  have hsubRaw6 :
      (c.firstPrime + (M - s.regs 6 % c.firstPrime)) % M =
        c.firstPrime - s.regs 6 % c.firstPrime := by
    simpa [rW] using hsubRaw
  have hoffM6 :
      ((c.firstPrime - s.regs 6 % c.firstPrime) % c.firstPrime) % M =
        (c.firstPrime - s.regs 6 % c.firstPrime) % c.firstPrime := by
    simpa [rW] using hoffM
  have hR5 : s.regs 5 = 0 := by simpa [rR] using hR
  have hOne : 1 + (M - 1) = M := by
    have := M_pos
    omega
  simp [markSetup, markPrefix, preSignal, Cfg.coreBody, firstOffset,
    arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rR, rPi, rP, rJ, rW, hR5, hpmod, hpNe,
    hremM6, hsubRaw6, hoffM6, hOne]

/-- A live reset-independent round computes the two live addresses and exact
product value. -/
theorem roundBeforeProd_live (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hj : s.regs rJ < c.segLen)
    (hA : c.arrayLen < M) :
    let q := arun idx s (roundBeforeProd c)
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
  have hj4 : s.regs 4 < c.segLen := by simpa [rJ] using hj
  have hjmod4 : s.regs 4 % M = s.regs 4 := by simpa [rJ] using hjmod
  have hjLmod4 : (s.regs 4 + c.segLen) % M =
      s.regs 4 + c.segLen := by simpa [rJ] using hjLmod
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hOne : 1 + (M - 1) = M := by
    have := M_pos
    omega
  set_option maxRecDepth 10000 in
    simp [roundBeforeProd, markRound, markPrefix, preSignal, Cfg.coreBody,
      prodUpdate, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rW, rP, rJ, hgate, hj4, hLM, hjmod4, hjLmod4,
      h1mod, hOne]
    rfl

/-- Exact array effect of the reset-independent part of one live mark. -/
theorem arun_markRound_live (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hj : s.regs rJ < c.segLen)
    (hpPos : 0 < s.regs rP)
    (hpSqM : s.regs rP * s.regs rP < M)
    (hnM : s.regs rW + s.regs rJ < M)
    (hA : c.arrayLen < M) :
    let j := s.regs rJ
    let p := s.regs rP
    let w := s.regs rW
    let out := arun idx s (markRound c)
    out.arr j = prodUpdate (s.arr j) p ∧
      out.arr (j + c.segLen) = flagUpdate (w + j)
        (s.arr (j + c.segLen)) p ∧
      ∀ x, x ≠ j → x ≠ j + c.segLen → out.arr x = s.arr x := by
  let j := s.regs rJ
  let p := s.regs rP
  let w := s.regs rW
  let s0 := arun idx s (roundBeforeProd c)
  let s1 := astep idx s0 (.store 25 30)
  let s2 := arun idx s1 (markBetweenStores c)
  let s3 := astep idx s2 (.store 26 38)
  have hb := roundBeforeProd_live c idx s hgate hj hA
  have hLpos : 0 < c.segLen := by omega
  have hne : j ≠ j + c.segLen := by omega
  have hs0arr : s0.arr = s.arr :=
    arun_arr_frame idx (roundBeforeProd c) s (by rfl)
  have hs0r25 : s0.regs 25 = j := hb.1
  have hs0r26 : s0.regs 26 = j + c.segLen := hb.2.1
  have hs0r30 : s0.regs 30 = prodUpdate (s.arr j) p := hb.2.2.1
  have hs0rp : s0.regs rP = p := hb.2.2.2.1
  have hs0rw : s0.regs rW = w := hb.2.2.2.2
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
  have hs2flag : s2.regs 38 =
      flagUpdate (w + j) (s.arr (j + c.segLen)) p := by
    rw [markBetweenStores_live c idx s1 j p w hs1r25 hs1r26 hs1rp hs1rw
      hnM hpPos hpSqM, hs1flag]
  have hdecomp : arun idx s (markRound c) =
      arun idx s3 (roundAfterFlag c) := by
    rw [markRound_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append]
    rfl
  have hfinal (x : Nat) : (arun idx s (markRound c)).arr x = s3.arr x := by
    rw [hdecomp]
    exact congrFun (arun_arr_frame idx (roundAfterFlag c) s3 (by rfl)) x
  refine ⟨?_, ?_, ?_⟩
  · rw [hfinal]
    change s3.arr j = _
    have hnot : j ≠ s2.regs 26 := by rw [hs2r26]; exact hne
    change (s2.writeArr (s2.regs 26) (s2.regs 38)).arr j = _
    rw [AState.writeArr_arr_ne s2 _ hnot, congrFun hs2arr]
    simpa [j, p] using hs1prod
  · rw [hfinal]
    change s3.arr (j + c.segLen) = _
    change (s2.writeArr (s2.regs 26) (s2.regs 38)).arr
      (j + c.segLen) = _
    rw [hs2r26, AState.writeArr_arr_self, hs2flag]
  · intro x hxj hxflag
    rw [hfinal]
    change s3.arr x = s.arr x
    have hnotFlag : x ≠ s2.regs 26 := by rw [hs2r26]; exact hxflag
    change (s2.writeArr (s2.regs 26) (s2.regs 38)).arr x = s.arr x
    rw [AState.writeArr_arr_ne s2 _ hnotFlag, congrFun hs2arr]
    change s1.arr x = s.arr x
    have hnotProd : x ≠ s0.regs 25 := by rw [hs0r25]; exact hxj
    change (s0.writeArr (s0.regs 25) (s0.regs 30)).arr x = s.arr x
    rw [AState.writeArr_arr_ne s0 _ hnotProd]
    exact congrFun hs0arr x

/-- Exact first marking update after the production window-start reset. -/
theorem arun_markPrefix_live_start (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 1)
    (hR : s.regs rR = 0)
    (hpPos : 0 < c.firstPrime)
    (hpLeL : c.firstPrime ≤ c.segLen)
    (hpM : c.firstPrime < M)
    (hpSqM : c.firstPrime * c.firstPrime < M)
    (hnM : s.regs rW + firstOffset (s.regs rW) c.firstPrime < M)
    (hA : c.arrayLen < M) :
    let j := firstOffset (s.regs rW) c.firstPrime
    let out := arun idx s (markPrefix c)
    out.arr j = prodUpdate (s.arr j) c.firstPrime ∧
      out.arr (j + c.segLen) = flagUpdate (s.regs rW + j)
        (s.arr (j + c.segLen)) c.firstPrime ∧
      ∀ x, x ≠ j → x ≠ j + c.segLen → out.arr x = s.arr x := by
  let j := firstOffset (s.regs rW) c.firstPrime
  let q := arun idx s (markSetup c)
  have hs := arun_markSetup_start c idx s hR hpPos hpM
  have hqarr : q.arr = s.arr :=
    arun_arr_frame idx (markSetup c) s (by rfl)
  have hj : j < c.segLen := by
    have hjp : j < c.firstPrime := by
      exact Nat.mod_lt _ hpPos
    omega
  have hm := arun_markRound_live c idx q
    (by rw [hs.2.2.2.2]; exact hgate)
    (by rw [hs.2.2.1]; exact hj)
    (by rw [hs.2.1]; exact hpPos)
    (by rw [hs.2.1]; exact hpSqM)
    (by rw [hs.2.2.2.1, hs.2.2.1]; exact hnM) hA
  rw [markPrefix_eq_setup_round, arun_append]
  refine ⟨?_, ?_, ?_⟩
  · change (arun idx q (markRound c)).arr j = _
    calc
      _ = (arun idx q (markRound c)).arr (q.regs rJ) := by rw [hs.2.2.1]
      _ = prodUpdate (q.arr (q.regs rJ)) (q.regs rP) := hm.1
      _ = prodUpdate (s.arr j) c.firstPrime := by
        rw [hs.2.2.1, hs.2.1, congrFun hqarr]
  · change (arun idx q (markRound c)).arr (j + c.segLen) = _
    calc
      _ = (arun idx q (markRound c)).arr
          (q.regs rJ + c.segLen) := by rw [hs.2.2.1]
      _ = flagUpdate (q.regs rW + q.regs rJ)
          (q.arr (q.regs rJ + c.segLen)) (q.regs rP) := hm.2.1
      _ = flagUpdate (s.regs rW + j)
          (s.arr (j + c.segLen)) c.firstPrime := by
        rw [hs.2.2.2.1, hs.2.2.1, hs.2.1, congrFun hqarr]
  · intro x hxj hxflag
    change (arun idx q (markRound c)).arr x = s.arr x
    calc
      _ = q.arr x := hm.2.2 x (by rw [hs.2.2.1]; exact hxj)
        (by rw [hs.2.2.1]; exact hxflag)
      _ = s.arr x := congrFun hqarr x

end LeanCompCert.Ports.ArraySegMobiusMark

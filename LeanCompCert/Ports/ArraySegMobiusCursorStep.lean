import LeanCompCert.Ports.ArraySegMobiusCursor

/-!
# Composed segmented-Möbius cursor steps

This file composes the small verified cursor slices.  It supplies the two
semantic transitions needed by the later marking-loop induction: continuing
with the current prime, and moving to the following prime-table entry.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- The clamp slice exposed without unfolding the rest of the production
body. -/
theorem cursorIndex_eq_instrs (c : Cfg) : cursorIndex c =
    [ .scalar (.binop 41 .add (.reg rPi) (.reg 40))
    , .scalar (.binop 42 .gt (.reg 41) (.reg rLimit))
    , .scalar (.binop 43 .sub (.lit 1) (.reg 42))
    , .scalar (.binop 44 .mul (.reg 43) (.reg 41))
    , .scalar (.binop 45 .mul (.reg 42) (.reg rLimit))
    , .scalar (.binop rPi .add (.reg 44) (.reg 45)) ] := by
  rfl

/-- With advance one at the selected table limit, the production clamp keeps
the cursor at that limit.  This is the fixed point used by the slack marking
iterations after every required prime has been exhausted. -/
theorem cursorIndex_advance_terminal (c : Cfg) (idx : Nat) (s : AState)
    (hadvance : s.regs 40 = 1)
    (hterminal : s.regs rPi = s.regs rLimit)
    (hnextM : s.regs rLimit + 1 < M) :
    let q := arun idx s (cursorIndex c)
    q.regs rPi = s.regs rLimit ∧ q.regs rP = s.regs rP ∧
      q.regs rJ = s.regs rJ ∧ q.regs rW = s.regs rW ∧
      q.regs rLimit = s.regs rLimit := by
  have hpiEq2 : s.regs 2 = s.regs 128 := by
    simpa [rPi, rLimit] using hterminal
  have hnextMod : (s.regs 128 + 1) % M = s.regs 128 + 1 := by
    apply Nat.mod_eq_of_lt
    simpa [rLimit] using hnextM
  have hrawGt : s.regs 128 < s.regs 128 + 1 := by omega
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hOne : 1 + (M - 1) = M := by
    have := M_pos
    omega
  have hlimitMod : s.regs 128 % M = s.regs 128 := by
    apply Nat.mod_eq_of_lt
    have hnextM128 : s.regs 128 + 1 < M := by
      simpa [rLimit] using hnextM
    exact Nat.lt_trans (Nat.lt_succ_self _) hnextM128
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [cursorIndex_eq_instrs, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, rPi, rLimit, hadvance, hpiEq2, hnextMod,
      hrawGt, h1mod, hOne, hlimitMod]
  · exact arun_reg_frame idx rP (cursorIndex c) s (by rfl)
  · exact arun_reg_frame idx rJ (cursorIndex c) s (by rfl)
  · exact arun_reg_frame idx rW (cursorIndex c) s (by rfl)
  · exact arun_reg_frame idx rLimit (cursorIndex c) s (by rfl)

/-- After a live multiple was marked, the production cursor keeps its index
and prime and advances the multiple by exactly that prime. -/
theorem roundAfterFlag_hold (c : Cfg) (idx : Nat) (s : AState)
    (pi p j w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hinR : s.regs 21 = 1)
    (hpi : s.regs rPi = pi)
    (hp : s.regs rP = p)
    (hj : s.regs rJ = j)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hpiLe : pi ≤ limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hnextM : j + p < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s (roundAfterFlag c)
    out.regs rPi = pi ∧ out.regs rP = p ∧
      out.regs rJ = j + p ∧ out.regs rW = w ∧
      out.regs rLimit = limit ∧ out.arr = s.arr := by
  let s0 := arun idx s (cursorGate c)
  let s1 := arun idx s0 (cursorIndex c)
  let s2 := arun idx s1 (cursorLoad c)
  let s3 := arun idx s2 (cursorPrime c)
  let s4 := arun idx s3 (cursorOffset c)
  let s5 := arun idx s4 (cursorFinish c)
  rcases cursorGate_marked c idx s hgate hinR with
    ⟨hs0adv, hs0pi, hs0p, hs0j, hs0w, hs0limit⟩
  change s0.regs 40 = 0 at hs0adv
  change s0.regs rPi = s.regs rPi at hs0pi
  change s0.regs rP = s.regs rP at hs0p
  change s0.regs rJ = s.regs rJ at hs0j
  change s0.regs rW = s.regs rW at hs0w
  change s0.regs rLimit = s.regs rLimit at hs0limit
  rcases cursorIndex_hold c idx s0 hs0adv
      (by rw [hs0pi, hs0limit, hpi, hlimit]; exact hpiLe)
      (by rw [hs0limit, hlimit]; exact hlimitM) with
    ⟨hs1pi, hs1p, hs1j, hs1w, hs1limit⟩
  change s1.regs rPi = s0.regs rPi at hs1pi
  change s1.regs rP = s0.regs rP at hs1p
  change s1.regs rJ = s0.regs rJ at hs1j
  change s1.regs rW = s0.regs rW at hs1w
  change s1.regs rLimit = s0.regs rLimit at hs1limit
  have hs1adv : s1.regs 40 = 0 := by
    rw [arun_reg_frame idx 40 (cursorIndex c) s0 (by rfl), hs0adv]
  rcases cursorLoad_table c idx s1 pi
      (by rw [hs1pi, hs0pi, hpi])
      (Nat.le_trans hpiLe hlimitLe) hA with
    ⟨_hs2load, hs2pi, hs2p, hs2j, hs2w, hs2limit, hs2adv⟩
  change s2.regs 47 = s1.arr (c.primeBase + pi) at _hs2load
  change s2.regs rPi = pi at hs2pi
  change s2.regs rP = s1.regs rP at hs2p
  change s2.regs rJ = s1.regs rJ at hs2j
  change s2.regs rW = s1.regs rW at hs2w
  change s2.regs rLimit = s1.regs rLimit at hs2limit
  change s2.regs 40 = s1.regs 40 at hs2adv
  have hs2adv0 : s2.regs 40 = 0 := hs2adv.trans hs1adv
  rcases cursorPrime_hold c idx s2 p j hs2adv0
      (by rw [hs2p, hs1p, hs0p, hp])
      (by rw [hs2j, hs1j, hs0j, hj]) hpM hnextM with
    ⟨hs3p, hs3next, hs3keep, hs3pi, hs3j, hs3w, hs3limit⟩
  change s3.regs rP = p at hs3p
  change s3.regs 49 = j + p at hs3next
  change s3.regs 48 = 1 at hs3keep
  change s3.regs rPi = s2.regs rPi at hs3pi
  change s3.regs rJ = j at hs3j
  change s3.regs rW = s2.regs rW at hs3w
  change s3.regs rLimit = s2.regs rLimit at hs3limit
  rcases cursorOffset_first c idx s3 w p
      (by rw [hs3w, hs2w, hs1w, hs0w, hw]) hs3p
      hpPos hpM with
    ⟨_hs4off, hs4p, hs4pi, _hs4j, hs4w, hs4limit,
      hs4adv, hs4keep, hs4next⟩
  change s4.regs 54 = firstOffset w p at _hs4off
  change s4.regs rP = p at hs4p
  change s4.regs rPi = s3.regs rPi at hs4pi
  change s4.regs rJ = s3.regs rJ at _hs4j
  change s4.regs rW = w at hs4w
  change s4.regs rLimit = s3.regs rLimit at hs4limit
  change s4.regs 40 = s3.regs 40 at hs4adv
  change s4.regs 48 = s3.regs 48 at hs4keep
  change s4.regs 49 = s3.regs 49 at hs4next
  have hs3adv : s3.regs 40 = 0 := by
    rw [arun_reg_frame idx 40 (cursorPrime c) s2 (by rfl), hs2adv0]
  have hs4adv0 : s4.regs 40 = 0 := hs4adv.trans hs3adv
  have hs4keep1 : s4.regs 48 = 1 := hs4keep.trans hs3keep
  rcases cursorFinish_hold c idx s4 (j + p) hs4adv0 hs4keep1
      (hs4next.trans hs3next) hnextM with
    ⟨hs5j, hs5pi, hs5p, hs5w, hs5limit⟩
  change s5.regs rJ = j + p at hs5j
  change s5.regs rPi = s4.regs rPi at hs5pi
  change s5.regs rP = s4.regs rP at hs5p
  change s5.regs rW = s4.regs rW at hs5w
  change s5.regs rLimit = s4.regs rLimit at hs5limit
  have hdecomp : arun idx s (roundAfterFlag c) = s5 := by
    simp only [roundAfterFlag_eq_cursorSlices, arun_append]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdecomp]
    exact hs5pi.trans (hs4pi.trans (hs3pi.trans hs2pi))
  · rw [hdecomp]
    exact hs5p.trans hs4p
  · rw [hdecomp]
    exact hs5j
  · rw [hdecomp]
    exact hs5w.trans hs4w
  · rw [hdecomp]
    exact hs5limit.trans <| hs4limit.trans <| hs3limit.trans <|
      hs2limit.trans <| hs1limit.trans <| hs0limit.trans hlimit
  · rw [hdecomp]
    exact Eq.trans (arun_arr_frame idx (cursorFinish c) s4 (by rfl)) <|
      Eq.trans (arun_arr_frame idx (cursorOffset c) s3 (by rfl)) <|
        Eq.trans (arun_arr_frame idx (cursorPrime c) s2 (by rfl)) <|
          Eq.trans (arun_arr_frame idx (cursorLoad c) s1 (by rfl)) <|
            Eq.trans (arun_arr_frame idx (cursorIndex c) s0 (by rfl))
              (arun_arr_frame idx (cursorGate c) s (by rfl))

/-- After the current prime has no multiple left in the window, the
production cursor advances exactly one table slot.  The new prime starts at
its first window offset, except that reaching the cursor limit installs the
explicit `segLen + 1` sentinel. -/
theorem roundAfterFlag_advance (c : Cfg) (idx : Nat) (s : AState)
    (pi p w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hinR : s.regs 21 = 0)
    (hpi : s.regs rPi = pi)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hpiLt : pi < limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (htable : s.arr (c.primeBase + (pi + 1)) = p)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s (roundAfterFlag c)
    out.regs rPi = pi + 1 ∧ out.regs rP = p ∧
      out.regs rJ = (if pi + 1 = limit then c.segLen + 1
        else firstOffset w p) ∧
      out.regs rW = w ∧ out.regs rLimit = limit ∧ out.arr = s.arr := by
  let s0 := arun idx s (cursorGate c)
  let s1 := arun idx s0 (cursorIndex c)
  let s2 := arun idx s1 (cursorLoad c)
  let s3 := arun idx s2 (cursorPrime c)
  let s4 := arun idx s3 (cursorOffset c)
  let s5 := arun idx s4 (cursorFinish c)
  rcases cursorGate_exhausted c idx s hgate hinR with
    ⟨hs0adv, hs0pi, _hs0p, _hs0j, hs0w, hs0limit⟩
  change s0.regs 40 = 1 at hs0adv
  change s0.regs rPi = s.regs rPi at hs0pi
  change s0.regs rW = s.regs rW at hs0w
  change s0.regs rLimit = s.regs rLimit at hs0limit
  rcases cursorIndex_advance c idx s0 hs0adv
      (by rw [hs0pi, hs0limit, hpi, hlimit]; exact hpiLt)
      (by rw [hs0limit, hlimit]; exact hlimitM) with
    ⟨hs1pi, _hs1p, _hs1j, hs1w, hs1limit⟩
  change s1.regs rPi = s0.regs rPi + 1 at hs1pi
  change s1.regs rW = s0.regs rW at hs1w
  change s1.regs rLimit = s0.regs rLimit at hs1limit
  have hs1piNext : s1.regs rPi = pi + 1 := by
    rw [hs1pi, hs0pi, hpi]
  have hs1adv : s1.regs 40 = 1 := by
    rw [arun_reg_frame idx 40 (cursorIndex c) s0 (by rfl), hs0adv]
  rcases cursorLoad_table c idx s1 (pi + 1) hs1piNext
      (Nat.le_trans (by omega : pi + 1 ≤ limit) hlimitLe) hA with
    ⟨hs2load, hs2pi, _hs2p, _hs2j, hs2w, hs2limit, hs2adv⟩
  change s2.regs 47 = s1.arr (c.primeBase + (pi + 1)) at hs2load
  change s2.regs rPi = pi + 1 at hs2pi
  change s2.regs rW = s1.regs rW at hs2w
  change s2.regs rLimit = s1.regs rLimit at hs2limit
  change s2.regs 40 = s1.regs 40 at hs2adv
  have hs1arr : s1.arr = s.arr :=
    Eq.trans (arun_arr_frame idx (cursorIndex c) s0 (by rfl))
      (arun_arr_frame idx (cursorGate c) s (by rfl))
  have hs2loadP : s2.regs 47 = p := by
    rw [hs2load, congrFun hs1arr, htable]
  have hs2adv1 : s2.regs 40 = 1 := hs2adv.trans hs1adv
  rcases cursorPrime_advance c idx s2 p hs2adv1 hs2loadP hpM with
    ⟨hs3p, hs3drop, hs3pi, _hs3j, hs3w, hs3limit, hs3adv⟩
  change s3.regs rP = p at hs3p
  change s3.regs 48 = 0 at hs3drop
  change s3.regs rPi = s2.regs rPi at hs3pi
  change s3.regs rW = s2.regs rW at hs3w
  change s3.regs rLimit = s2.regs rLimit at hs3limit
  change s3.regs 40 = 1 at hs3adv
  rcases cursorOffset_first c idx s3 w p
      (by rw [hs3w, hs2w, hs1w, hs0w, hw]) hs3p hpPos hpM with
    ⟨hs4off, hs4p, hs4pi, _hs4j, hs4w, hs4limit,
      hs4adv, hs4drop, _hs4next⟩
  change s4.regs 54 = firstOffset w p at hs4off
  change s4.regs rP = p at hs4p
  change s4.regs rPi = s3.regs rPi at hs4pi
  change s4.regs rW = w at hs4w
  change s4.regs rLimit = s3.regs rLimit at hs4limit
  change s4.regs 40 = s3.regs 40 at hs4adv
  change s4.regs 48 = s3.regs 48 at hs4drop
  have hs4adv1 : s4.regs 40 = 1 := hs4adv.trans hs3adv
  have hs4drop0 : s4.regs 48 = 0 := hs4drop.trans hs3drop
  have hs4piNext : s4.regs rPi = pi + 1 :=
    hs4pi.trans (hs3pi.trans hs2pi)
  have hs4limitVal : s4.regs rLimit = limit :=
    hs4limit.trans <| hs3limit.trans <| hs2limit.trans <|
      hs1limit.trans <| hs0limit.trans hlimit
  have hLM : c.segLen + 1 < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  have hdecomp : arun idx s (roundAfterFlag c) = s5 := by
    simp only [roundAfterFlag_eq_cursorSlices, arun_append]
    rfl
  have hs5piBase : s5.regs rPi = s4.regs rPi :=
    arun_reg_frame idx rPi (cursorFinish c) s4 (by rfl)
  have hs5pBase : s5.regs rP = s4.regs rP :=
    arun_reg_frame idx rP (cursorFinish c) s4 (by rfl)
  have hs5wBase : s5.regs rW = s4.regs rW :=
    arun_reg_frame idx rW (cursorFinish c) s4 (by rfl)
  have hs5limitBase : s5.regs rLimit = s4.regs rLimit :=
    arun_reg_frame idx rLimit (cursorFinish c) s4 (by rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdecomp]
    exact hs5piBase.trans hs4piNext
  · rw [hdecomp]
    exact hs5pBase.trans hs4p
  · rw [hdecomp]
    by_cases hterm : pi + 1 = limit
    · rw [if_pos hterm]
      rcases cursorFinish_terminal c idx s4 hs4adv1 hs4drop0
          (by rw [hs4piNext, hs4limitVal, hterm]) hLM with
        ⟨hj, _⟩
      exact hj
    · rw [if_neg hterm]
      rcases cursorFinish_advance c idx s4 (firstOffset w p)
          hs4adv1 hs4drop0 hs4off
          (by rw [hs4piNext, hs4limitVal]; exact hterm)
          (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpPos) (Nat.le_of_lt hpM)) with
        ⟨hj, _⟩
      exact hj
  · rw [hdecomp]
    exact hs5wBase.trans hs4w
  · rw [hdecomp]
    exact hs5limitBase.trans hs4limitVal
  · rw [hdecomp]
    exact Eq.trans (arun_arr_frame idx (cursorFinish c) s4 (by rfl)) <|
      Eq.trans (arun_arr_frame idx (cursorOffset c) s3 (by rfl)) <|
        Eq.trans (arun_arr_frame idx (cursorPrime c) s2 (by rfl)) <|
          Eq.trans (arun_arr_frame idx (cursorLoad c) s1 (by rfl)) hs1arr

/-- After the selected table limit has been reached, an exhausted marking
iteration is a cursor fixed point: it reloads the terminal table cell and
reinstalls the explicit out-of-window sentinel. -/
theorem roundAfterFlag_advance_terminal (c : Cfg) (idx : Nat) (s : AState)
    (p w limit : Nat)
    (hgate : s.regs 8 = 1)
    (hinR : s.regs 21 = 0)
    (hpi : s.regs rPi = limit)
    (hw : s.regs rW = w)
    (hlimit : s.regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (htable : s.arr (c.primeBase + limit) = p)
    (hpPos : 0 < p)
    (hpM : p < M)
    (hA : c.arrayLen < M) :
    let out := arun idx s (roundAfterFlag c)
    out.regs rPi = limit ∧ out.regs rP = p ∧
      out.regs rJ = c.segLen + 1 ∧ out.regs rW = w ∧
      out.regs rLimit = limit ∧ out.arr = s.arr := by
  let s0 := arun idx s (cursorGate c)
  let s1 := arun idx s0 (cursorIndex c)
  let s2 := arun idx s1 (cursorLoad c)
  let s3 := arun idx s2 (cursorPrime c)
  let s4 := arun idx s3 (cursorOffset c)
  let s5 := arun idx s4 (cursorFinish c)
  rcases cursorGate_exhausted c idx s hgate hinR with
    ⟨hs0adv, hs0pi, _hs0p, _hs0j, hs0w, hs0limit⟩
  change s0.regs 40 = 1 at hs0adv
  change s0.regs rPi = s.regs rPi at hs0pi
  change s0.regs rW = s.regs rW at hs0w
  change s0.regs rLimit = s.regs rLimit at hs0limit
  have hlimitNextM : s0.regs rLimit + 1 < M := by
    rw [hs0limit, hlimit]
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  rcases cursorIndex_advance_terminal c idx s0 hs0adv
      (by rw [hs0pi, hs0limit, hpi, hlimit]) hlimitNextM with
    ⟨hs1pi, _hs1p, _hs1j, hs1w, hs1limit⟩
  change s1.regs rPi = s0.regs rLimit at hs1pi
  change s1.regs rW = s0.regs rW at hs1w
  change s1.regs rLimit = s0.regs rLimit at hs1limit
  have hs1piLimit : s1.regs rPi = limit := by
    rw [hs1pi, hs0limit, hlimit]
  have hs1adv : s1.regs 40 = 1 := by
    rw [arun_reg_frame idx 40 (cursorIndex c) s0 (by rfl), hs0adv]
  rcases cursorLoad_table c idx s1 limit hs1piLimit hlimitLe hA with
    ⟨hs2load, hs2pi, _hs2p, _hs2j, hs2w, hs2limit, hs2adv⟩
  change s2.regs 47 = s1.arr (c.primeBase + limit) at hs2load
  change s2.regs rPi = limit at hs2pi
  change s2.regs rW = s1.regs rW at hs2w
  change s2.regs rLimit = s1.regs rLimit at hs2limit
  change s2.regs 40 = s1.regs 40 at hs2adv
  have hs1arr : s1.arr = s.arr :=
    Eq.trans (arun_arr_frame idx (cursorIndex c) s0 (by rfl))
      (arun_arr_frame idx (cursorGate c) s (by rfl))
  have hs2loadP : s2.regs 47 = p := by
    rw [hs2load, congrFun hs1arr, htable]
  have hs2adv1 : s2.regs 40 = 1 := hs2adv.trans hs1adv
  rcases cursorPrime_advance c idx s2 p hs2adv1 hs2loadP hpM with
    ⟨hs3p, hs3drop, hs3pi, _hs3j, hs3w, hs3limit, hs3adv⟩
  change s3.regs rP = p at hs3p
  change s3.regs 48 = 0 at hs3drop
  change s3.regs rPi = s2.regs rPi at hs3pi
  change s3.regs rW = s2.regs rW at hs3w
  change s3.regs rLimit = s2.regs rLimit at hs3limit
  change s3.regs 40 = 1 at hs3adv
  rcases cursorOffset_first c idx s3 w p
      (by rw [hs3w, hs2w, hs1w, hs0w, hw]) hs3p hpPos hpM with
    ⟨_hs4off, hs4p, hs4pi, _hs4j, hs4w, hs4limit,
      hs4adv, hs4drop, _hs4next⟩
  change s4.regs rP = p at hs4p
  change s4.regs rPi = s3.regs rPi at hs4pi
  change s4.regs rW = w at hs4w
  change s4.regs rLimit = s3.regs rLimit at hs4limit
  change s4.regs 40 = s3.regs 40 at hs4adv
  change s4.regs 48 = s3.regs 48 at hs4drop
  have hs4adv1 : s4.regs 40 = 1 := hs4adv.trans hs3adv
  have hs4drop0 : s4.regs 48 = 0 := hs4drop.trans hs3drop
  have hs4piLimit : s4.regs rPi = limit :=
    hs4pi.trans (hs3pi.trans hs2pi)
  have hs4limitVal : s4.regs rLimit = limit :=
    hs4limit.trans <| hs3limit.trans <| hs2limit.trans <|
      hs1limit.trans <| hs0limit.trans hlimit
  have hLM : c.segLen + 1 < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  rcases cursorFinish_terminal c idx s4 hs4adv1 hs4drop0
      (hs4piLimit.trans hs4limitVal.symm) hLM with
    ⟨hs5j, hs5pi, hs5p, hs5w, hs5limit⟩
  have hdecomp : arun idx s (roundAfterFlag c) = s5 := by
    simp only [roundAfterFlag_eq_cursorSlices, arun_append]
    rfl
  rw [hdecomp]
  refine ⟨hs5pi.trans hs4piLimit, hs5p.trans hs4p, hs5j,
    hs5w.trans hs4w, hs5limit.trans hs4limitVal, ?_⟩
  exact Eq.trans (arun_arr_frame idx (cursorFinish c) s4 (by rfl)) <|
    Eq.trans (arun_arr_frame idx (cursorOffset c) s3 (by rfl)) <|
      Eq.trans (arun_arr_frame idx (cursorPrime c) s2 (by rfl)) <|
        Eq.trans (arun_arr_frame idx (cursorLoad c) s1 (by rfl)) hs1arr

end LeanCompCert.Ports.ArraySegMobiusMark

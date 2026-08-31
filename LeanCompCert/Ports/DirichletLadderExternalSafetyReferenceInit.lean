import LeanCompCert.Ports.DirichletLadderExternalSafetyReference
import LeanCompCert.Verified.ArrayRegFrame

/-! Historical initializer state projected to the independent reference. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

/-- The thirteen persistent historical registers, read as a reference state. -/
def refStateOf (s : AState) : RefState :=
  ⟨s.regs rViol, s.regs rPrevTag, s.regs rPrevBlk, s.regs rPrevUpper,
    s.regs rPrevBit, s.regs rFirstBit, s.regs rTrI0, s.regs rSj0,
    s.regs rTrI1, s.regs rSj1, s.regs rPrevLast, s.regs rPrevConj,
    s.regs rPrevDig⟩

private theorem table_frame (c : Cfg) (r : Nat)
    (hr : r ≠ 20) (hr' : r ≠ 21) (s : AState) :
    (arun 0 s c.tableBlock).regs r = s.regs r := by
  apply LeanCompCert.Verified.ArrayRegFrame.arun_frame
  simp [LeanCompCert.Verified.ArrayRegFrame.writes,
    LeanCompCert.Verified.ArrayRegFrame.instrWrites, Cfg.tableBlock,
    Cfg.tableEntryBlock, LeanCompCert.Verified.InstrBlock.sdest, mvl, hr, hr']
  intro x hx
  exact ⟨Ne.symm hr, Ne.symm hr'⟩

private theorem bitFold_le (v : Nat) (indices : List Nat) (init : Nat) :
    indices.foldl (fun total k => total + (v >>> k) % 2) init ≤
      init + indices.length := by
  induction indices generalizing init with
  | nil => simp
  | cons k rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      calc
        rest.foldl (fun total j => total + (v >>> j) % 2)
            (init + (v >>> k) % 2) ≤
          init + (v >>> k) % 2 + rest.length := ih _
        _ ≤ init + (rest.length + 1) := by
          have hm := Nat.mod_lt (v >>> k) (show 0 < 2 by omega)
          omega

private theorem momentFold_le (v : Nat) (indices : List Nat) (init : Nat)
    (hindices : ∀ k ∈ indices, k ≤ 7) :
    indices.foldl (fun total k => total + k * ((v >>> k) % 2)) init ≤
      init + 7 * indices.length := by
  induction indices generalizing init with
  | nil => simp
  | cons k rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hk : k ≤ 7 := hindices k (by simp)
      have hrest : ∀ j ∈ rest, j ≤ 7 := by
        intro j hj; exact hindices j (by simp [hj])
      calc
        rest.foldl (fun total j => total + j * ((v >>> j) % 2))
            (init + k * ((v >>> k) % 2)) ≤
          init + k * ((v >>> k) % 2) + 7 * rest.length := ih _ hrest
        _ ≤ init + 7 * (rest.length + 1) := by
          have hm := Nat.mod_lt (v >>> k) (show 0 < 2 by omega)
          have hmle : (v >>> k) % 2 ≤ 1 := by omega
          have hmul : k * ((v >>> k) % 2) ≤ 7 * 1 :=
            Nat.mul_le_mul hk hmle
          omega

theorem popc8_le (v : Nat) : popc8 v ≤ 8 := by
  simpa [popc8] using bitFold_le v (List.range 8) 0

theorem mom8_le (v : Nat) : mom8 v ≤ 56 := by
  have h := momentFold_le v (List.range 8) 0 (by
    intro k hk; have := List.mem_range.mp hk; omega)
  simpa [mom8] using h

theorem tblEntry_word (v : Nat) : tblEntry v < M := by
  have hp := popc8_le v
  have hm := mom8_le v
  simp only [tblEntry, M]
  omega

theorem tableEntryBlock_arr (c : Cfg) (v k : Nat) (s : AState)
    (haddr : c.tblBase + v < M) (hval : tblEntry v < M) :
    (arun 0 s (c.tableEntryBlock v)).arr k =
      if k = c.tblBase + v then tblEntry v else s.arr k := by
  simp [Cfg.tableEntryBlock, mvl, arun, astep, AState.writeReg,
    AState.writeArr, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
    Nat.mod_eq_of_lt haddr, Nat.mod_eq_of_lt hval]

private theorem tableEntries_preserve_below
    (c : Cfg) (entries : List Nat) (k : Nat) (s : AState)
    (hlen : c.arrayLen < M) (hk : k < c.tblBase)
    (hentries : ∀ v ∈ entries, v < 256) :
    (arun 0 s (entries.flatMap c.tableEntryBlock)).arr k = s.arr k := by
  induction entries generalizing s with
  | nil => rfl
  | cons v rest ih =>
      simp only [List.flatMap_cons, arun_append]
      rw [ih (arun 0 s (c.tableEntryBlock v))
        (by intro x hx; exact hentries x (by simp [hx]))]
      have hv : v < 256 := hentries v (by simp)
      have haddr : c.tblBase + v < M := by
        have h := hlen
        change c.tblBase + 256 < M at h
        omega
      rw [tableEntryBlock_arr c v k s haddr (tblEntry_word v)]
      simp [show k ≠ c.tblBase + v by omega]

theorem historical_symbolicEntry_record_cell
    (c : Cfg) (words : List Nat) (k : Nat)
    (hlen : c.arrayLen < M) (hk : k < c.tblBase) :
    (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
      c (wordsArray words)).arr k = words.getD k 0 := by
  simp only [LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry,
    Cfg.initBlock, arun_append]
  simp only [arun, astep, mvl, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
    AState.writeReg_arr]
  rw [show c.tableBlock = (List.range 256).flatMap c.tableEntryBlock by rfl]
  rw [tableEntries_preserve_below c (List.range 256) k _ hlen hk
    (by intro v hv; exact List.mem_range.mp hv)]
  rfl

private theorem tableRange_cell
    (c : Cfg) (n v : Nat) (s : AState)
    (hlen : c.tblBase + n < M) (hv : v < n) :
    (arun 0 s ((List.range n).flatMap c.tableEntryBlock)).arr
      (c.tblBase + v) = tblEntry v := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, arun_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hnaddr : c.tblBase + n < M := by omega
      rw [tableEntryBlock_arr c n (c.tblBase + v)
        (arun 0 s ((List.range n).flatMap c.tableEntryBlock)) hnaddr
        (tblEntry_word n)]
      by_cases hev : v = n
      · subst v; simp
      · rw [if_neg (by omega)]
        exact ih (by omega) (by omega)

theorem historical_symbolicEntry_table_cell
    (c : Cfg) (words : List Nat) (v : Nat)
    (hlen : c.arrayLen < M) (hv : v < 256) :
    (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
      c (wordsArray words)).arr (c.tblBase + v) = tblEntry v := by
  simp only [LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry,
    Cfg.initBlock, arun_append, arun, astep, mvl,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
    AState.writeReg_arr]
  rw [show c.tableBlock = (List.range 256).flatMap c.tableEntryBlock by rfl]
  apply tableRange_cell c 256 v
  · change c.tblBase + 256 < M at hlen
    exact hlen
  · exact hv

set_option maxRecDepth 10000 in
theorem historical_symbolicEntry_refState
    (c : Cfg) (words : List Nat) :
    refStateOf
      (LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry
        c (wordsArray words)) = refInit := by
  simp only [refStateOf, refInit, RefState.mk.injEq,
    LeanCompCert.Ports.DirichletLadderExternalDenotation.symbolicEntry,
    Cfg.initBlock, arun_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [arun, astep, mvl,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
      AState.writeReg, initialAStateWithArray, rViol, rPrevTag, rPrevBlk,
      rPrevUpper, rPrevBit, rFirstBit, rTrI0, rSj0, rTrI1, rSj1,
      rPrevLast, rPrevConj, rPrevDig, M]
    try rw [table_frame c _ (by decide) (by decide)]
    simp [initialState, M]

end LeanCompCert.Ports.DirichletLadderExternalSafety

import LeanCompCert.Ports.PsiRuntimePrimeTable
import LeanCompCert.Verified.ArrayFoldBridge
import LeanCompCert.Verified.PackedSieve

/-! # Source semantics of the compiled psi composite-mark stage

This proves one arbitrary compiled grid round marks exactly the decoded
candidate/divisor pair.  It is symbolic in the grid size and never evaluates
a production prime table in Lean. -/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

def psiRootMarkWidth (m : PsiRuntimeMeta) : Nat := max 1 (m.divCap - 1)
def psiRootMarkN (m : PsiRuntimeMeta) (index : Nat) : Nat :=
  index / psiRootMarkWidth m + 2
def psiRootMarkD (m : PsiRuntimeMeta) (index : Nat) : Nat :=
  index % psiRootMarkWidth m + 2
def psiRootMarkHit (m : PsiRuntimeMeta) (index : Nat) : Nat :=
  if psiRootMarkD m index * psiRootMarkD m index ≤ psiRootMarkN m index ∧
      psiRootMarkN m index % psiRootMarkD m index = 0 then 1 else 0

theorem psiRootMarkWidth_eq (m : PsiRuntimeMeta) (hDiv : 2 ≤ m.divCap) :
    psiRootMarkWidth m = m.divCap - 1 := by
  simp [psiRootMarkWidth, Nat.max_eq_right (by omega : 1 ≤ m.divCap - 1)]

theorem psiRootMark_index_bounds (m : PsiRuntimeMeta) {index : Nat}
    (hDiv : 2 ≤ m.divCap)
    (hi : index < (psiRootMarkProgram m).loopCount) :
    psiRootMarkN m index ≤ m.root ∧
      2 ≤ psiRootMarkD m index ∧ psiRootMarkD m index ≤ m.divCap := by
  have hw : 0 < psiRootMarkWidth m := by
    have hle : 1 ≤ max 1 (m.divCap - 1) := Nat.le_max_left _ _
    simpa [psiRootMarkWidth] using (Nat.lt_of_lt_of_le (by decide : 0 < 1) hle)
  have hwidth := psiRootMarkWidth_eq m hDiv
  have hi' : index < (m.root - 1) * psiRootMarkWidth m := by
    simpa [psiRootMarkProgram, hwidth] using hi
  have hq : index / psiRootMarkWidth m < m.root - 1 := by
    apply Nat.div_lt_of_lt_mul
    simpa [Nat.mul_comm] using hi'
  have hRootSub : 0 < m.root - 1 := by
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hq
  have hRoot : 2 ≤ m.root := by omega
  have hr := Nat.mod_lt index hw
  have hdlt : index % psiRootMarkWidth m < m.divCap - 1 := by
    simpa [hwidth] using hr
  constructor
  · change index / psiRootMarkWidth m + 2 ≤ m.root
    omega
  · constructor
    · change 2 ≤ index % psiRootMarkWidth m + 2
      omega
    · change index % psiRootMarkWidth m + 2 ≤ m.divCap
      omega

theorem psiRootMarkBody_spec (m : PsiRuntimeMeta) (index : Nat) (s : AState)
    (hDiv : 2 ≤ m.divCap)
    (hArray : m.arrayLen < M)
    (hLoopM : (psiRootMarkProgram m).loopCount < M)
    (hRootM : m.root < M)
    (hDivM : m.divCap < M)
    (hSquareM : m.divCap * m.divCap < M)
    (hi : index < (psiRootMarkProgram m).loopCount) :
    AllDefined m.arrayLen index s (psiRootMarkBody m) ∧
      ∀ x, (arun index s (psiRootMarkBody m)).arr x =
        if x = (if psiRootMarkHit m index = 1 then
          m.markBase + psiRootMarkN m index else m.markSink) then
          psiRootMarkHit m index else s.arr x := by
  have hb := psiRootMark_index_bounds m hDiv hi
  have hiM : index % M = index :=
    Nat.mod_eq_of_lt (Nat.lt_trans hi hLoopM)
  have hwPos : 0 < psiRootMarkWidth m := by
    have hle : 1 ≤ max 1 (m.divCap - 1) := Nat.le_max_left _ _
    simpa [psiRootMarkWidth] using (Nat.lt_of_lt_of_le (by decide : 0 < 1) hle)
  have hwLe : psiRootMarkWidth m ≤ m.divCap := by
    rw [psiRootMarkWidth_eq m hDiv]
    omega
  have hwM : psiRootMarkWidth m % M = psiRootMarkWidth m :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hwLe hDivM)
  have hwM' : max 1 (m.divCap - 1) % M = max 1 (m.divCap - 1) := by
    simpa [psiRootMarkWidth] using hwM
  have hwMod0 : psiRootMarkWidth m % M ≠ 0 := by rw [hwM]; omega
  have hwMod0' : max 1 (m.divCap - 1) % M ≠ 0 := by
    simpa [psiRootMarkWidth] using hwMod0
  have hnM : psiRootMarkN m index % M = psiRootMarkN m index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hb.1 hRootM)
  have hdM : psiRootMarkD m index % M = psiRootMarkD m index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hb.2.2 hDivM)
  have hnRawM : (index / psiRootMarkWidth m + 2) % M =
      index / psiRootMarkWidth m + 2 := by simpa [psiRootMarkN] using hnM
  have hnRawM' : (index / max 1 (m.divCap - 1) + 2) % M =
      index / max 1 (m.divCap - 1) + 2 := by
    simpa [psiRootMarkWidth] using hnRawM
  have hdRawM : (index % psiRootMarkWidth m + 2) % M =
      index % psiRootMarkWidth m + 2 := by simpa [psiRootMarkD] using hdM
  have hdRawM' : (index % max 1 (m.divCap - 1) + 2) % M =
      index % max 1 (m.divCap - 1) + 2 := by
    simpa [psiRootMarkWidth] using hdRawM
  have hd0 : psiRootMarkD m index ≠ 0 := by omega
  have hdPos : 0 < psiRootMarkD m index := by omega
  have hOneM : 1 % M = 1 := Nat.mod_eq_of_lt (by decide)
  have hPredM : (M - 1) % M = M - 1 := Nat.mod_eq_of_lt (by
    exact Nat.sub_lt (by decide) (by decide))
  have hCancelM : (1 % M + (M - 1) % M) % M = 0 := by
    rw [hOneM, hPredM]
    rw [show 1 + (M - 1) = M by omega]
    exact Nat.mod_self M
  have hMsum : 1 + (M - 1) = M := by omega
  have hremM : (psiRootMarkN m index % psiRootMarkD m index) % M =
      psiRootMarkN m index % psiRootMarkD m index := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_trans (Nat.mod_lt _ hdPos)
      (Nat.lt_of_le_of_lt hb.2.2 hDivM)
  have hddM : (psiRootMarkD m index * psiRootMarkD m index) % M =
      psiRootMarkD m index * psiRootMarkD m index := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hb.2.2 hb.2.2) hSquareM
  have hsink : m.markSink < m.arrayLen := by simp [PsiRuntimeMeta.arrayLen]
  have hsinkM : m.markSink % M = m.markSink :=
    Nat.mod_eq_of_lt (Nat.lt_trans hsink hArray)
  have hncell : m.markBase + psiRootMarkN m index < m.arrayLen := by
    simp only [PsiRuntimeMeta.arrayLen, PsiRuntimeMeta.markSink]
    omega
  have hncellM : (m.markBase + psiRootMarkN m index) % M =
      m.markBase + psiRootMarkN m index :=
    Nat.mod_eq_of_lt (Nat.lt_trans hncell hArray)
  have hncellM' : (psiRootMarkN m index + m.markBase) % M =
      psiRootMarkN m index + m.markBase := by
    simpa [Nat.add_comm] using hncellM
  let sd := arun index s (psiRootMarkDecode m)
  have hDecode : AllDefined m.arrayLen index s (psiRootMarkDecode m) := by
    simp [psiRootMarkDecode, AllDefined, ADefined, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, hiM, hwM, hwMod0', M_pos]
  have sd11 : sd.regs 11 = psiRootMarkN m index := by
    simp [sd, psiRootMarkDecode, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, psiRootMarkN,
      psiRootMarkWidth, hiM, hwM', hwMod0', hnRawM']
  have sd13 : sd.regs 13 = psiRootMarkD m index := by
    simp [sd, psiRootMarkDecode, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, psiRootMarkD,
      psiRootMarkWidth, hiM, hwM', hwMod0', hdRawM']
  let sw := arun index sd psiRootMarkWitness
  have hWitness : AllDefined m.arrayLen index sd psiRootMarkWitness := by
    simp [psiRootMarkWitness, AllDefined, ADefined, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, sd11, sd13, hd0, hdM]
  have sw15 : sw.regs 15 =
      (if psiRootMarkD m index * psiRootMarkD m index ≤
          psiRootMarkN m index then 1 else 0) := by
    simp [sw, psiRootMarkWitness, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, sd11, sd13, hddM, hnM]
  have sw17 : sw.regs 17 =
      (if psiRootMarkN m index % psiRootMarkD m index = 0 then 1 else 0) := by
    simp [sw, psiRootMarkWitness, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, sd11, sd13, hd0, hdM, hremM]
  have sw11 : sw.regs 11 = psiRootMarkN m index := by
    simp [sw, psiRootMarkWitness, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, sd11]
  let st := arun index sw (psiRootMarkTarget m)
  have hTarget : AllDefined m.arrayLen index sw (psiRootMarkTarget m) := by
    simp [psiRootMarkTarget, AllDefined, ADefined, astep, sval, sdest,
      denoteOperand, denoteOp]
  have st18 : st.regs 18 = psiRootMarkHit m index := by
    simp [st, psiRootMarkTarget, psiRootMarkHit, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, RegState.set, sw15, sw17]
    by_cases hsq : psiRootMarkD m index * psiRootMarkD m index ≤
        psiRootMarkN m index
    · by_cases hrem : psiRootMarkN m index % psiRootMarkD m index = 0
      · simp [hsq, hrem, hOneM]
      · simp [hsq, hrem]
    · simp [hsq]
  have st23 : st.regs 23 =
      if psiRootMarkHit m index = 1 then
        m.markBase + psiRootMarkN m index else m.markSink := by
    simp [st, psiRootMarkTarget, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, sw15, sw17, sw11,
      psiRootMarkHit]
    by_cases hsq : psiRootMarkD m index * psiRootMarkD m index ≤
        psiRootMarkN m index
    · by_cases hrem : psiRootMarkN m index % psiRootMarkD m index = 0
      · simp [hsq, hrem, hOneM, hMsum, hncellM']
        rw [Nat.add_comm]
      · simp [hsq, hrem, hsinkM, hOneM, hPredM,
          Nat.add_mod, Nat.mul_mod, hCancelM, hMsum]
    · simp [hsq, hsinkM, hOneM, hPredM,
        Nat.add_mod, Nat.mul_mod, hCancelM, hMsum]
  have hDefined : AllDefined m.arrayLen index s (psiRootMarkBody m) := by
    unfold psiRootMarkBody
    rw [show psiRootMarkDecode m ++ psiRootMarkWitness ++
        psiRootMarkTarget m ++ [.store 23 18] =
        psiRootMarkDecode m ++ (psiRootMarkWitness ++
          (psiRootMarkTarget m ++ [.store 23 18])) by
        simp [List.append_assoc]]
    rw [AllDefined_append]
    refine ⟨hDecode, ?_⟩
    rw [AllDefined_append]
    refine ⟨hWitness, ?_⟩
    rw [AllDefined_append]
    refine ⟨hTarget, ?_⟩
    simp only [AllDefined, ADefined]
    rw [st23]
    split
    · exact ⟨hncell, trivial⟩
    · exact ⟨hsink, trivial⟩
  refine ⟨hDefined, ?_⟩
  have hsdArr : sd.arr = s.arr := by
    simp [sd, psiRootMarkDecode, arun, astep, AState.writeReg]
  have hswArr : sw.arr = s.arr := by
    simp [sw, psiRootMarkWitness, arun, astep, AState.writeReg, hsdArr]
  have hstArr : st.arr = s.arr := by
    simp [st, psiRootMarkTarget, arun, astep, AState.writeReg, hswArr]
  intro x
  simp only [psiRootMarkBody, arun_append]
  change (st.writeArr (st.regs 23) (st.regs 18)).arr x = _
  simp [AState.writeArr, st23, st18, hstArr]

theorem psiRootMarkBody_defined (m : PsiRuntimeMeta) (index : Nat) (s : AState)
    (hDiv : 2 ≤ m.divCap) (hArray : m.arrayLen < M)
    (hLoopM : (psiRootMarkProgram m).loopCount < M)
    (hRootM : m.root < M) (hDivM : m.divCap < M)
    (hSquareM : m.divCap * m.divCap < M)
    (hi : index < (psiRootMarkProgram m).loopCount) :
    AllDefined m.arrayLen index s (psiRootMarkBody m) :=
  (psiRootMarkBody_spec m index s hDiv hArray hLoopM hRootM hDivM
    hSquareM hi).1

def psiRootMarkFoldPrefix (m : PsiRuntimeMeta) (arr : Nat → Nat)
    (k : Nat) : AState :=
  (List.range k).foldl (fun state index =>
      arun index state (psiRootMarkBody m))
    (initialAStateWithArray arr)

def psiRootMarkSeen (m : PsiRuntimeMeta) (k x : Nat) : Prop :=
  ∃ index, index < k ∧ psiRootMarkN m index = x ∧
    psiRootMarkHit m index = 1

noncomputable instance psiRootMarkSeenDecidable (m : PsiRuntimeMeta)
    (k x : Nat) : Decidable (psiRootMarkSeen m k x) :=
  Classical.propDecidable _

/-- Every logical root-table cell after an arbitrary compiled-loop prefix.
The proof is symbolic in `k`; no production-sized fold is reduced by Lean. -/
theorem psiRootMarkFoldPrefix_cell (m : PsiRuntimeMeta) (k x : Nat)
    (hDiv : 2 ≤ m.divCap)
    (hArray : m.arrayLen < M)
    (hLoopM : (psiRootMarkProgram m).loopCount < M)
    (hRootM : m.root < M)
    (hDivM : m.divCap < M)
    (hSquareM : m.divCap * m.divCap < M)
    (hk : k ≤ (psiRootMarkProgram m).loopCount)
    (hx : x ≤ m.root) :
    (psiRootMarkFoldPrefix m (fun _ => 0) k).arr (m.markBase + x) =
      if psiRootMarkSeen m k x then 1 else 0 := by
  classical
  have hxsink : m.markBase + x ≠ m.markSink := by
    simp only [PsiRuntimeMeta.markSink]
    omega
  induction k with
  | zero =>
      simp [psiRootMarkFoldPrefix, psiRootMarkSeen, initialAStateWithArray]
  | succ k ih =>
      have hklt : k < (psiRootMarkProgram m).loopCount := by omega
      have hkpre : k ≤ (psiRootMarkProgram m).loopCount := by omega
      let prev := psiRootMarkFoldPrefix m (fun _ => 0) k
      have hprev : prev.arr (m.markBase + x) =
          if psiRootMarkSeen m k x then 1 else 0 := ih hkpre
      have hstep := (psiRootMarkBody_spec m k prev hDiv hArray hLoopM
        hRootM hDivM hSquareM hklt).2 (m.markBase + x)
      have hseen : psiRootMarkSeen m (k + 1) x ↔
          psiRootMarkSeen m k x ∨
            (psiRootMarkN m k = x ∧ psiRootMarkHit m k = 1) := by
        constructor
        · rintro ⟨i, hi, hnx, hhit⟩
          by_cases hik : i < k
          · exact Or.inl ⟨i, hik, hnx, hhit⟩
          · right
            have hieq : i = k := by omega
            simpa [hieq] using And.intro hnx hhit
        · rintro (h | ⟨hnx, hhit⟩)
          · obtain ⟨i, hi, hnx, hhit⟩ := h
            exact ⟨i, by omega, hnx, hhit⟩
          · exact ⟨k, by omega, hnx, hhit⟩
      have hfold : psiRootMarkFoldPrefix m (fun _ => 0) (k + 1) =
          arun k prev (psiRootMarkBody m) := by
        simp [psiRootMarkFoldPrefix, prev, List.range_succ,
          List.foldl_append]
      rw [hfold, hstep]
      by_cases hold : psiRootMarkSeen m k x
      · by_cases hhit : psiRootMarkHit m k = 1
        · by_cases hnx : psiRootMarkN m k = x
          · simp [hseen, hold, hhit, hnx]
          · have hxne : m.markBase + x ≠
                m.markBase + psiRootMarkN m k := by omega
            have hxn : x ≠ psiRootMarkN m k := Ne.symm hnx
            simp [hseen, hold, hhit, hnx, hxn, hxne, hprev]
        · simp [hseen, hold, hhit, hprev, hxsink]
      · by_cases hhit : psiRootMarkHit m k = 1
        · by_cases hnx : psiRootMarkN m k = x
          · simp [hseen, hold, hhit, hnx]
          · have hxne : m.markBase + x ≠
                m.markBase + psiRootMarkN m k := by omega
            have hxn : x ≠ psiRootMarkN m k := Ne.symm hnx
            simp [hseen, hold, hhit, hnx, hxn, hxne, hprev]
        · simp [hseen, hold, hhit, hprev, hxsink]

/-- At the full trip count, the compiled marker has seen `x` exactly when it
has a divisor in the configured finite witness range. -/
theorem psiRootMarkSeen_full_iff (m : PsiRuntimeMeta) (x : Nat)
    (hDiv : 2 ≤ m.divCap) (hx2 : 2 ≤ x) (hxRoot : x ≤ m.root) :
    psiRootMarkSeen m (psiRootMarkProgram m).loopCount x ↔
      ∃ d, 2 ≤ d ∧ d ≤ m.divCap ∧ d * d ≤ x ∧ x % d = 0 := by
  have hwidth := psiRootMarkWidth_eq m hDiv
  constructor
  · rintro ⟨index, hi, hnx, hhit⟩
    have hb := psiRootMark_index_bounds m hDiv hi
    have hwitness : psiRootMarkD m index * psiRootMarkD m index ≤
          psiRootMarkN m index ∧
        psiRootMarkN m index % psiRootMarkD m index = 0 := by
      by_cases h : psiRootMarkD m index * psiRootMarkD m index ≤
            psiRootMarkN m index ∧
          psiRootMarkN m index % psiRootMarkD m index = 0
      · exact h
      · simp [psiRootMarkHit, h] at hhit
    refine ⟨psiRootMarkD m index, hb.2.1, hb.2.2, ?_, ?_⟩
    · simpa [hnx] using hwitness.1
    · simpa [hnx] using hwitness.2
  · rintro ⟨d, hd2, hdCap, hsq, hdiv⟩
    let q := x - 2
    let r := d - 2
    let index := q * psiRootMarkWidth m + r
    have hr : r < psiRootMarkWidth m := by
      dsimp only [r]
      rw [hwidth]
      omega
    have hq : q < m.root - 1 := by
      dsimp only [q]
      omega
    have hdecode : index / psiRootMarkWidth m = q ∧
        index % psiRootMarkWidth m = r := by
      have hw : 0 < psiRootMarkWidth m := by omega
      dsimp only [index]
      constructor
      · rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.div_eq_of_lt hr,
          Nat.add_zero]
      · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hn : psiRootMarkN m index = x := by
      simp [psiRootMarkN, hdecode.1, q]
      omega
    have hd : psiRootMarkD m index = d := by
      simp [psiRootMarkD, hdecode.2, r]
      omega
    have hi : index < (psiRootMarkProgram m).loopCount := by
      have hi0 : index < (q + 1) * psiRootMarkWidth m := by
        dsimp only [index]
        rw [Nat.add_mul]
        omega
      have hi1 : (q + 1) * psiRootMarkWidth m ≤
          (m.root - 1) * psiRootMarkWidth m :=
        Nat.mul_le_mul_right (psiRootMarkWidth m) (by omega)
      have hi1' : (q + 1) * psiRootMarkWidth m ≤
          (psiRootMarkProgram m).loopCount := by
        simpa [psiRootMarkProgram, hwidth] using hi1
      exact Nat.lt_of_lt_of_le hi0 hi1'
    refine ⟨index, hi, hn, ?_⟩
    simp [psiRootMarkHit, hn, hd, hsq, hdiv]

def psiRootMarkFold (m : PsiRuntimeMeta) (arr : Nat → Nat) : AState :=
  psiRootMarkFoldPrefix m arr (psiRootMarkProgram m).loopCount

def psiRootMarkedState (m : PsiRuntimeMeta) (arr : Nat → Nat) : AState :=
  arun 0 (psiRootMarkFold m arr) (psiRootMarkProgram m).epilogue

theorem psiRootMarkProgram_runFromArray (m : PsiRuntimeMeta)
    (arr : Nat → Nat)
    (hDiv : 2 ≤ m.divCap)
    (hArray : m.arrayLen < M)
    (hLoopM : (psiRootMarkProgram m).loopCount < M)
    (hRootM : m.root < M)
    (hDivM : m.divCap < M)
    (hSquareM : m.divCap * m.divCap < M) :
    (psiRootMarkProgram m).runFromArray arr =
      some (psiRootMarkedState m arr) := by
  apply AProgram.runFromArray_eq_foldl_mem
    (P := fun _ => True)
    (step := fun index state => arun index state (psiRootMarkBody m))
    (fin := fun state => arun 0 state (psiRootMarkProgram m).epilogue)
    (s₀ := initialAStateWithArray arr)
  · rfl
  · trivial
  · intro index state hi _
    apply denoteAInstrs_eq_arun
    exact psiRootMarkBody_defined m index state hDiv hArray hLoopM hRootM
      hDivM hSquareM hi
  · intros
    trivial
  · intro state _
    apply denoteAInstrs_eq_arun
    simp [psiRootMarkProgram, AllDefined, ADefined]

def PsiRootTrialComposite (m : PsiRuntimeMeta) (x : Nat) : Prop :=
  ∃ d, 2 ≤ d ∧ d ≤ m.divCap ∧ d * d ≤ x ∧ x % d = 0

noncomputable instance psiRootTrialCompositeDecidable (m : PsiRuntimeMeta)
    (x : Nat) : Decidable (PsiRootTrialComposite m x) :=
  Classical.propDecidable _

/-- A configured divisor cap covering the square root makes the finite
compiled witness search extensionally equal to ordinary compositeness. -/
theorem psiRootTrialComposite_iff_not_prime (m : PsiRuntimeMeta) {x : Nat}
    (hx2 : 2 ≤ x) (hxRoot : x ≤ m.root)
    (hCap : m.root < (m.divCap + 1) * (m.divCap + 1)) :
    PsiRootTrialComposite m x ↔
      ¬LeanCompCert.Verified.PackedSieve.IsPrime x := by
  constructor
  · rintro ⟨d, hd2, _hdCap, hdsq, hdmod⟩ hprime
    have hdvd : d ∣ x := Nat.dvd_of_mod_eq_zero hdmod
    rcases hprime.eq_one_or_self hdvd with hd1 | hdx
    · omega
    · subst d
      have hxPos : 0 < x := by omega
      have hxOne : 1 < x := by omega
      have hxLtSq : x < x * x := by
        have h := (Nat.mul_lt_mul_left hxPos).mpr hxOne
        simpa using h
      exact (Nat.not_lt_of_ge hdsq) hxLtSq
  · intro hprime
    obtain ⟨d, hdPrime, hdDvd, hdSq⟩ :=
      LeanCompCert.Verified.PackedSieve.exists_prime_factor_le_sqrt hx2 hprime
    have hdCap : d ≤ m.divCap := by
      apply Classical.byContradiction
      intro hnot
      have hnext : m.divCap + 1 ≤ d := by omega
      have hsq : (m.divCap + 1) * (m.divCap + 1) ≤ d * d :=
        Nat.mul_le_mul hnext hnext
      omega
    exact ⟨d, hdPrime.two_le, hdCap, hdSq,
      Nat.mod_eq_zero_of_dvd hdDvd⟩

theorem psiRootMarkedState_cell (m : PsiRuntimeMeta) (x : Nat)
    (hDiv : 2 ≤ m.divCap)
    (hArray : m.arrayLen < M)
    (hLoopM : (psiRootMarkProgram m).loopCount < M)
    (hRootM : m.root < M)
    (hDivM : m.divCap < M)
    (hSquareM : m.divCap * m.divCap < M)
    (hx2 : 2 ≤ x) (hxRoot : x ≤ m.root) :
    (psiRootMarkedState m (fun _ => 0)).arr (m.markBase + x) =
      if PsiRootTrialComposite m x then 1 else 0 := by
  classical
  have hcell := psiRootMarkFoldPrefix_cell m
    (psiRootMarkProgram m).loopCount x hDiv hArray hLoopM hRootM hDivM
    hSquareM (Nat.le_refl _) hxRoot
  have hseen := psiRootMarkSeen_full_iff m x hDiv hx2 hxRoot
  have hstate :
      (psiRootMarkedState m (fun _ => 0)).arr (m.markBase + x) =
        (psiRootMarkFoldPrefix m (fun _ => 0)
          (psiRootMarkProgram m).loopCount).arr (m.markBase + x) := by
    simp [psiRootMarkedState, psiRootMarkFold, psiRootMarkProgram, arun,
      astep, AState.writeReg]
  have hiff : psiRootMarkSeen m (psiRootMarkProgram m).loopCount x ↔
      PsiRootTrialComposite m x := by
    simpa only [PsiRootTrialComposite] using hseen
  rw [hstate, hcell]
  by_cases hs : psiRootMarkSeen m (psiRootMarkProgram m).loopCount x
  · have hc : PsiRootTrialComposite m x := hiff.mp hs
    simp [hs, hc]
  · have hc : ¬PsiRootTrialComposite m x := fun hc => hs (hiff.mpr hc)
    simp [hs, hc]

theorem psiRootMarkedState_cell_eq_zero_iff_prime (m : PsiRuntimeMeta)
    (x : Nat)
    (hDiv : 2 ≤ m.divCap)
    (hArray : m.arrayLen < M)
    (hLoopM : (psiRootMarkProgram m).loopCount < M)
    (hRootM : m.root < M)
    (hDivM : m.divCap < M)
    (hSquareM : m.divCap * m.divCap < M)
    (hCap : m.root < (m.divCap + 1) * (m.divCap + 1))
    (hx2 : 2 ≤ x) (hxRoot : x ≤ m.root) :
    (psiRootMarkedState m (fun _ => 0)).arr (m.markBase + x) = 0 ↔
      LeanCompCert.Verified.PackedSieve.IsPrime x := by
  rw [psiRootMarkedState_cell m x hDiv hArray hLoopM hRootM hDivM
    hSquareM hx2 hxRoot]
  have hcomp := psiRootTrialComposite_iff_not_prime m hx2 hxRoot hCap
  by_cases hc : PsiRootTrialComposite m x
  · have hnp := hcomp.mp hc
    simp [hc, hnp]
  · have hp : LeanCompCert.Verified.PackedSieve.IsPrime x :=
      Classical.not_not.mp (fun hnp => hc (hcomp.mpr hnp))
    simp [hc, hp]

#print axioms psiRootMark_index_bounds
#print axioms psiRootMarkBody_spec
#print axioms psiRootMarkBody_defined
#print axioms psiRootMarkFoldPrefix_cell
#print axioms psiRootMarkSeen_full_iff
#print axioms psiRootMarkProgram_runFromArray
#print axioms psiRootTrialComposite_iff_not_prime
#print axioms psiRootMarkedState_cell
#print axioms psiRootMarkedState_cell_eq_zero_iff_prime

end LeanCompCert.Ports.PsiSegSieve

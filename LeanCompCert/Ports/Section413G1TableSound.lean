import LeanCompCert.Ports.Section413G1TableProgram

/-!
# Source soundness of the Section 4.13 G2 table carrier

The certificate program uses two array planes above the original sweep's
three planes.  This file proves that those extra writes cannot influence the
verified sweep: registers below 256 and cells in the original array extent
simulate the original machine instruction for instruction.
-/

namespace LeanCompCert.Ports.Section413G1TableSound

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413G1Program
open LeanCompCert.Ports.Section413G1TableProgram
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells (encodeZ)

def CoreEq (c : Cfg) (a b : AState) : Prop :=
  (∀ j, j < LeanCompCert.Ports.Section413G1Program.regCount →
    a.regs j = b.regs j) ∧
  ∀ i, i < c.arrayLen → a.arr i = b.arr i

theorem operand_eq {a b : AState} {rc : Nat}
    (h : ∀ j, j < rc → a.regs j = b.regs j) (k : Nat)
    (o : Operand) (ho : o.WF rc) :
    denoteOperand k a.regs o = denoteOperand k b.regs o := by
  cases o with
  | reg j => exact h j ho
  | lit | idx => rfl

theorem adefined_core {c : Cfg} {k : Nat} {a b : AState} {i : AInstr}
    (heq : CoreEq c a b)
    (hwf : i.WF LeanCompCert.Ports.Section413G1Program.regCount)
    (hdef : ADefined c.arrayLen k a i) : ADefined c.arrayLen k b i := by
  rcases heq with ⟨hr, ha⟩
  cases i with
  | scalar instr =>
      cases instr with
      | mov d o => trivial
      | binop d op l r =>
          simp only [AInstr.WF, Instr.WF] at hwf
          simpa only [ADefined, operand_eq hr k l hwf.2.1,
            operand_eq hr k r hwf.2.2] using hdef
  | load d r =>
      simp only [AInstr.WF] at hwf
      simpa only [ADefined, hr r hwf.2] using hdef
  | store r v =>
      simp only [AInstr.WF] at hwf
      simpa only [ADefined, hr r hwf.1] using hdef

theorem astep_core {c : Cfg} {k : Nat} {a b : AState} {i : AInstr}
    (heq : CoreEq c a b)
    (hwf : i.WF LeanCompCert.Ports.Section413G1Program.regCount)
    (hdef : ADefined c.arrayLen k a i) :
    CoreEq c (astep k a i) (astep k b i) := by
  rcases heq with ⟨hr, ha⟩
  have hdefb := adefined_core ⟨hr, ha⟩ hwf hdef
  constructor
  · intro j hj
    cases i with
    | scalar instr =>
        cases instr with
        | mov d o =>
            simp only [AInstr.WF, Instr.WF] at hwf
            simp only [astep, AState.writeReg]
            split
            · exact operand_eq hr k o hwf.2
            · exact hr j hj
        | binop d op l r =>
            simp only [AInstr.WF, Instr.WF] at hwf
            simp only [astep, AState.writeReg,
              LeanCompCert.Verified.InstrBlock.sdest,
              LeanCompCert.Verified.InstrBlock.sval]
            split
            · rw [operand_eq hr k l hwf.2.1, operand_eq hr k r hwf.2.2]
            · exact hr j hj
    | load d r =>
        simp only [AInstr.WF] at hwf
        simp only [astep, AState.writeReg]
        split
        · calc
            a.arr (a.regs r) = b.arr (a.regs r) := ha _ hdef
            _ = b.arr (b.regs r) := congrArg b.arr (hr r hwf.2)
        · exact hr j hj
    | store r v => exact hr j hj
  · intro x hx
    cases i with
    | scalar instr => exact ha x hx
    | load d r => exact ha x hx
    | store r v =>
        simp only [AInstr.WF] at hwf
        have hraddr := hr r hwf.1
        have hrval := hr v hwf.2
        simp only [astep, AState.writeArr]
        by_cases hxa : x = a.regs r
        · rw [if_pos hxa, ← hraddr, if_pos hxa, hrval]
        · have hxb : x ≠ b.regs r := by simpa only [← hraddr] using hxa
          rw [if_neg hxa, if_neg hxb]
          exact ha x hx

theorem arun_core {c : Cfg} {k : Nat} :
    ∀ (l : List AInstr) (a b : AState),
      CoreEq c a b →
      (∀ i ∈ l, i.WF LeanCompCert.Ports.Section413G1Program.regCount) →
      AllDefined c.arrayLen k a l →
      CoreEq c (arun k a l) (arun k b l) := by
  intro l
  induction l with
  | nil => intro a b heq hwf hdef; exact heq
  | cons i rest ih =>
      intro a b heq hwf hdef
      have hiwf := hwf i (by simp)
      have hstep := astep_core heq hiwf hdef.1
      exact ih (astep k a i) (astep k b i) hstep
        (fun x hx => hwf x (List.mem_cons_of_mem i hx)) hdef.2

theorem arun_arr_outside {len k x : Nat} (hx : len ≤ x) :
    ∀ (l : List AInstr) (s : AState), AllDefined len k s l →
      (arun k s l).arr x = s.arr x := by
  intro l
  induction l with
  | nil => intro s h; rfl
  | cons i rest ih =>
      intro s h
      rw [arun_cons, ih (astep k s i) h.2]
      cases i with
      | scalar instr => rfl
      | load d r => rfl
      | store r v =>
          simp only [astep, AState.writeArr]
          have haddr : s.regs r < len := h.1
          rw [if_neg (by intro heq; subst x; omega)]

theorem body_wf256 (c : Cfg) :
    ∀ i ∈ c.body, i.WF LeanCompCert.Ports.Section413G1Program.regCount := by
  intro i hi
  exact (g1Program_wf c).2.2.1 i (by simpa [g1Program] using hi)

theorem finBody_regs_31_35 (c : Cfg) (k : Nat) (s : AState) (j : Nat)
    (hj : j = 31 ∨ j = 35) :
    (arun k s c.finBody).regs j = s.regs j := by
  apply LeanCompCert.Ports.Section413G1Denote.arun_regs_frame
  intro i hi
  have hall : c.finBody.all (fun x => decide
      (LeanCompCert.Ports.Section413G1Denote.adest x ≠ some j)) = true := by
    rcases hj with rfl | rfl <;> rfl
  exact of_decide_eq_true ((List.all_eq_true.mp hall) i hi)

set_option maxRecDepth 10000 in
theorem body_selector (c : Cfg)
    (hc : LeanCompCert.Ports.Section413G1Denote.Admissible c)
    (idx : Nat) (hidx : idx < c.loopCount) (s : AState) :
    let p := arun idx s c.body
    p.regs 31 = (c.tsel idx).X ∧ p.regs 35 = (c.tsel idx).isF := by
  rw [LeanCompCert.Ports.Section413G1Denote.body_eq_prefix_fin, arun_append]
  have h := LeanCompCert.Ports.Section413G1Denote.selTrialPassAWeightPassB_selector
    c hc idx hidx s
  exact ⟨(finBody_regs_31_35 c idx _ 31 (Or.inl rfl)).trans h.1,
    (finBody_regs_31_35 c idx _ 35 (Or.inr rfl)).trans h.2⟩

theorem tsel_store_product_le (c : Cfg)
    (hc : LeanCompCert.Ports.Section413G1Denote.Admissible c)
    (idx : Nat) (hidx : idx < c.loopCount) :
    (c.tsel idx).isF * (c.tsel idx).X ≤ c.cap := by
  by_cases hp : idx < c.phase1
  · simp [Cfg.tsel, hp, bnat]
  · have hphase : c.phase1 ≤ idx := Nat.le_of_not_gt hp
    have hidxM : idx < M := Nat.lt_trans hidx hc.loopLt
    have hphaseM : c.phase1 < M :=
      Nat.lt_of_le_of_lt (by simp [Cfg.loopCount]) hc.loopLt
    have hsub : tsub idx c.phase1 = idx - c.phase1 := by
      rw [tsub]
      have hsubM : idx - c.phase1 < M := by omega
      have heq : idx + (M - c.phase1) = (idx - c.phase1) + M := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hsubM]
    have hpPos : 0 < c.p := LeanCompCert.Ports.Section413G1Denote.p_pos c
    have htail : idx - c.phase1 < c.cap * c.p := by
      simp [Cfg.loopCount] at hidx
      omega
    have hx0 : (idx - c.phase1) / c.p < c.cap := by
      exact (Nat.div_lt_iff_lt_mul hpPos).2 htail
    have hcapM : c.cap < M := by
      have := hc.arrayLt
      simp [Cfg.arrayLen] at this
      omega
    have hxM : (idx - c.phase1) / c.p + 1 < M := by omega
    have hX : (c.tsel idx).X ≤ c.cap := by
      simp only [Cfg.tsel, hsub, Nat.mod_eq_of_lt hxM]
      omega
    have hF := LeanCompCert.Ports.Section413G1Denote.tsel_isF_le_one c idx
    rcases (by omega : (c.tsel idx).isF = 0 ∨ (c.tsel idx).isF = 1) with h | h <;>
      simp [h, hX]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem tableStore_core (c : Cfg) (hc : TableAdmissible c)
    (k : Nat) (s : AState) (hprod : s.regs 35 * s.regs 31 ≤ c.cap) :
    CoreEq c (arun k s (tableStoreBody c)) s := by
  constructor
  · intro j hj
    change j < 256 at hj
    apply LeanCompCert.Ports.Section413G1Denote.arun_regs_frame
    intro i hi
    simp only [tableStoreBody, tableStorePrep, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;>
      simp [LeanCompCert.Ports.Section413G1Denote.adest, rAddrLo, rAddrHi,
        rValLo, rValHi] <;> omega
  · intro i hi
    have hp := tableArrayLen_pos c
    have hmod : tableArrayLen c % M = tableArrayLen c :=
      Nat.mod_eq_of_lt hc.tableLt
    have hloLen : s.regs 35 * s.regs 31 + tableLo c < tableArrayLen c := by
      simp [tableLo, tableArrayLen]
      omega
    have hhiLen : s.regs 35 * s.regs 31 + tableHi c < tableArrayLen c := by
      simp [tableHi, tableArrayLen]
      omega
    have hloM := Nat.lt_trans hloLen hc.tableLt
    have hhiM := Nat.lt_trans hhiLen hc.tableLt
    have hloEval :
        (s.regs 35 * s.regs 31 + tableLo c) % M % tableArrayLen c % M =
          s.regs 35 * s.regs 31 + tableLo c := by
      rw [Nat.mod_eq_of_lt hloM, Nat.mod_eq_of_lt hloLen,
        Nat.mod_eq_of_lt hloM]
    have hhiEval :
        (s.regs 35 * s.regs 31 + tableHi c) % M % tableArrayLen c % M =
          s.regs 35 * s.regs 31 + tableHi c := by
      rw [Nat.mod_eq_of_lt hhiM, Nat.mod_eq_of_lt hhiLen,
        Nat.mod_eq_of_lt hhiM]
    have hneLo : i ≠ s.regs 35 * s.regs 31 + tableLo c := by
      intro heq
      have : c.arrayLen ≤ i := by
        simp [Cfg.arrayLen, tableLo] at heq ⊢
        omega
      omega
    have hneHi : i ≠ s.regs 35 * s.regs 31 + tableHi c := by
      intro heq
      have : c.arrayLen ≤ i := by
        simp [Cfg.arrayLen, tableHi] at heq ⊢
        omega
      omega
    simp [tableStoreBody, tableStorePrep, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, AState.writeArr, hmod, Nat.ne_of_gt hp,
      rAddrLo, rAddrHi, rValLo, rValHi, hloEval, hhiEval, hneLo, hneHi]

theorem CoreEq.trans {c : Cfg} {a b d : AState}
    (hab : CoreEq c a b) (hbd : CoreEq c b d) : CoreEq c a d := by
  exact ⟨fun j hj => (hab.1 j hj).trans (hbd.1 j hj),
    fun i hi => (hab.2 i hi).trans (hbd.2 i hi)⟩

theorem CoreEq.symm {c : Cfg} {a b : AState} (h : CoreEq c a b) :
    CoreEq c b a :=
  ⟨fun j hj => (h.1 j hj).symm, fun i hi => (h.2 i hi).symm⟩

def baseStep (c : Cfg) (idx : Nat) (s : AState) : AState :=
  arun idx s c.body

def basePrefix (c : Cfg) (k : Nat) : AState :=
  (List.range k).foldl (fun s idx => baseStep c idx s) (rawEntry c)

set_option maxRecDepth 10000 in
theorem basePrefix_succ (c : Cfg) (k : Nat) :
    basePrefix c (k + 1) = baseStep c k (basePrefix c k) := by
  unfold basePrefix
  rw [List.range_succ, List.foldl_append]
  rfl

def PairInv (c : Cfg) (a b : AState) : Prop :=
  CoreEq c a b ∧
  LeanCompCert.Ports.Section413G1Denote.MachineInv b ∧ WordInv a

theorem entry_pairInv (c : Cfg) (hc : TableAdmissible c) :
    PairInv c (rawEntry c) (rawEntry c) := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩, ?_, ?_⟩
  · exact LeanCompCert.Ports.Section413G1Denote.machineEntry_inv c hc.base
  · refine ⟨LeanCompCert.Ports.Section413G1Denote.arun_regs_lt
        0 c.init initialAState ?_ ?_,
      LeanCompCert.Ports.Section413G1Denote.arun_arr_lt
        0 c.init initialAState ?_ ?_⟩ <;>
      simp [initialAState, initialState, M]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem pair_step (c : Cfg) (hc : TableAdmissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (a b : AState) (h : PairInv c a b) :
    PairInv c (rawStep c idx a) (baseStep c idx b) := by
  rcases h with ⟨heq, hbinv, hainv⟩
  have hbdef := LeanCompCert.Ports.Section413G1Denote.body_defined
    c hc.base idx hidx b hbinv.1 hbinv.2.1
  have hbody : CoreEq c (arun idx a c.body) (arun idx b c.body) :=
    (arun_core c.body b a heq.symm (body_wf256 c) hbdef).symm
  have hsel := body_selector c hc.base idx hidx a
  have hstore := tableStore_core c hc idx (arun idx a c.body) (by
    rw [hsel.1, hsel.2]
    exact tsel_store_product_le c hc.base idx hidx)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [rawStep, baseStep, arun_append] using hstore.trans hbody
  · exact LeanCompCert.Ports.Section413G1Denote.body_machineInv
      c hc.base idx hidx b hbinv
  · exact extended_body_wordInv c idx a hainv

theorem parallel_prefix (c : Cfg) (hc : TableAdmissible c) :
    ∀ k, k ≤ c.loopCount →
      PairInv c
        ((List.range k).foldl (fun s idx => rawStep c idx s) (rawEntry c))
        (basePrefix c k) := by
  intro k
  induction k with
  | zero => intro hk; exact entry_pairInv c hc
  | succ k ih =>
      intro hk
      unfold basePrefix
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact pair_step c hc k (by omega) _ _ (ih (by omega))

theorem rawFinal_core_baseFinal (c : Cfg) (hc : TableAdmissible c) :
    CoreEq c (rawFinal c) (basePrefix c c.loopCount) := by
  exact (parallel_prefix c hc c.loopCount (Nat.le_refl _)).1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem basePrefix_obs (c : Cfg) (hc : TableAdmissible c) :
    ∀ k, k ≤ c.loopCount →
      LeanCompCert.Ports.Section413G1Denote.obsT (basePrefix c k) =
        LeanCompCert.Ports.Section413G1Sound.tRunUpto c k := by
  intro k
  induction k with
  | zero =>
      intro hk
      have hi := (LeanCompCert.Ports.Section413G1Denote.init_reaches_tInit c
        (by simp [Cfg.arrayLen]; omega)).2
      simpa only [basePrefix, rawEntry, List.range_zero, List.foldl_nil,
        LeanCompCert.Ports.Section413G1Sound.tRunUpto_zero] using hi
  | succ k ih =>
      intro hk
      have hp := parallel_prefix c hc k (by omega)
      have hInv := hp.2.1
      have hbody := LeanCompCert.Ports.Section413G1Denote.body_obs
        c hc.base k (by omega) (basePrefix c k) hInv.1 hInv.2.1
        hInv.2.2.1 hInv.2.2.2.1 hInv.2.2.2.2
      rw [LeanCompCert.Ports.Section413G1Sound.tRunUpto_succ, ← ih (by omega)]
      rw [basePrefix_succ]
      simpa only [baseStep] using hbody

theorem rawFinal_core_tRun (c : Cfg) (hc : TableAdmissible c) :
    (rawFinal c).regs rViol = c.tRun.viol ∧
      (rawFinal c).regs 12 = c.tRun.gLo ∧
      (rawFinal c).regs 13 = c.tRun.gHi := by
  have heq := rawFinal_core_baseFinal c hc
  have hobs := basePrefix_obs c hc c.loopCount (Nat.le_refl _)
  rw [← LeanCompCert.Ports.Section413G1Sound.tRun_eq_tRunUpto] at hobs
  exact ⟨(heq.1 rViol (by decide)).trans (congrArg TState.viol hobs),
    (heq.1 12 (by decide)).trans (congrArg TState.gLo hobs),
    (heq.1 13 (by decide)).trans (congrArg TState.gHi hobs)⟩

def rawPrefix (c : Cfg) (k : Nat) : AState :=
  (List.range k).foldl (fun s idx => rawStep c idx s) (rawEntry c)

set_option maxRecDepth 10000 in
theorem rawPrefix_succ (c : Cfg) (k : Nat) :
    rawPrefix c (k + 1) = rawStep c k (rawPrefix c k) := by
  unfold rawPrefix
  rw [List.range_succ, List.foldl_append]
  rfl

theorem rawFinal_eq_prefix (c : Cfg) : rawFinal c = rawPrefix c c.loopCount := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem tableStore_arr (c : Cfg) (hc : TableAdmissible c) (k : Nat)
    (s : AState) (hprod : s.regs 35 * s.regs 31 ≤ c.cap) (i : Nat) :
    (arun k s (tableStoreBody c)).arr i =
      if i = tableHi c + s.regs 35 * s.regs 31 then s.regs 35 * s.regs 13 % M
      else if i = tableLo c + s.regs 35 * s.regs 31 then
        s.regs 35 * s.regs 12 % M else s.arr i := by
  have hp := tableArrayLen_pos c
  have hmod : tableArrayLen c % M = tableArrayLen c :=
    Nat.mod_eq_of_lt hc.tableLt
  have hloLen : tableLo c + s.regs 35 * s.regs 31 < tableArrayLen c := by
    simp [tableLo, tableArrayLen]
    omega
  have hhiLen : tableHi c + s.regs 35 * s.regs 31 < tableArrayLen c := by
    simp [tableHi, tableArrayLen]
    omega
  have hloM := Nat.lt_trans hloLen hc.tableLt
  have hhiM := Nat.lt_trans hhiLen hc.tableLt
  have hloEval :
      (s.regs 35 * s.regs 31 + tableLo c) % M % tableArrayLen c % M =
        tableLo c + s.regs 35 * s.regs 31 := by
    rw [Nat.add_comm, Nat.mod_eq_of_lt hloM, Nat.mod_eq_of_lt hloLen,
      Nat.mod_eq_of_lt hloM]
  have hhiEval :
      (s.regs 35 * s.regs 31 + tableHi c) % M % tableArrayLen c % M =
        tableHi c + s.regs 35 * s.regs 31 := by
    rw [Nat.add_comm, Nat.mod_eq_of_lt hhiM, Nat.mod_eq_of_lt hhiLen,
      Nat.mod_eq_of_lt hhiM]
  simp [tableStoreBody, tableStorePrep, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, AState.writeArr, hmod, Nat.ne_of_gt hp,
    rAddrLo, rAddrHi, rValLo, rValHi, hloEval, hhiEval]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem rawStep_arr_high (c : Cfg) (hc : TableAdmissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (s : AState)
    (hs : WordInv s) (i : Nat) (hi : c.arrayLen ≤ i) :
    (rawStep c idx s).arr i =
      let z := c.tsel idx
      if i = tableHi c + z.isF * z.X then z.isF *
          (arun idx s c.body).regs 13 % M
      else if i = tableLo c + z.isF * z.X then z.isF *
          (arun idx s c.body).regs 12 % M
      else s.arr i := by
  let p := arun idx s c.body
  have hdef := LeanCompCert.Ports.Section413G1Denote.body_defined
    c hc.base idx hidx s hs.1 hs.2
  have hframe : p.arr i = s.arr i := arun_arr_outside hi c.body s hdef
  have hsel := body_selector c hc.base idx hidx s
  have hprod := tsel_store_product_le c hc.base idx hidx
  dsimp only at hsel
  have hpProd : p.regs 35 * p.regs 31 ≤ c.cap := by
    rw [hsel.1, hsel.2]
    exact hprod
  rw [rawStep, arun_append, tableStore_arr c hc idx p hpProd]
  rw [hsel.1, hsel.2, hframe]

theorem rawPrefix_wordInv (c : Cfg) (hc : TableAdmissible c) (k : Nat)
    (hk : k ≤ c.loopCount) : WordInv (rawPrefix c k) := by
  exact (parallel_prefix c hc k hk).2.2

theorem tsel_X_pos_of_isF_one (c : Cfg) (hc : TableAdmissible c)
    (idx : Nat) (hidx : idx < c.loopCount)
    (hF : (c.tsel idx).isF = 1) : 0 < (c.tsel idx).X := by
  have hphase : c.phase1 ≤ idx := by
    by_cases hp : idx < c.phase1
    · simp [Cfg.tsel, hp, bnat] at hF
    · omega
  have hidxM : idx < M := Nat.lt_trans hidx hc.base.loopLt
  have hphaseM : c.phase1 < M :=
    Nat.lt_of_le_of_lt (by simp [Cfg.loopCount]) hc.base.loopLt
  have hsubM : idx - c.phase1 < M := by omega
  have hsub : tsub idx c.phase1 = idx - c.phase1 := by
    rw [tsub]
    have heq : idx + (M - c.phase1) = (idx - c.phase1) + M := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hsubM]
  have hpPos : 0 < c.p :=
    LeanCompCert.Ports.Section413G1Denote.p_pos c
  have htail : idx - c.phase1 < c.cap * c.p := by
    simp only [Cfg.loopCount] at hidx
    omega
  have hx0 : (idx - c.phase1) / c.p < c.cap :=
    (Nat.div_lt_iff_lt_mul hpPos).2 htail
  have hcapM : c.cap < M := by
    have := hc.base.arrayLt
    simp [Cfg.arrayLen] at this
    omega
  have hxM : (idx - c.phase1) / c.p + 1 < M := by omega
  change 0 < ((tsub idx c.phase1 / c.p + 1) % M)
  simpa only [hsub, Nat.mod_eq_of_lt hxM] using
    (Nat.succ_pos ((idx - c.phase1) / c.p))

/-- The two producer table sentinels remain zero.  This is a symbolic loop
invariant; it does not evaluate the production sweep. -/
theorem rawPrefix_zero_cells (c : Cfg) (hc : TableAdmissible c) :
    ∀ k, k ≤ c.loopCount →
      (rawPrefix c k).arr (tableLo c) = 0 ∧
      (rawPrefix c k).arr (tableHi c) = 0 := by
  intro k
  induction k with
  | zero =>
      intro _
      have hlo1 : tableLo c ≠ 1 := by simp [tableLo]; omega
      have hhi1 : tableHi c ≠ 1 := by simp [tableHi]; omega
      simp [rawPrefix, rawEntry, Cfg.init,
        LeanCompCert.Ports.CDEMAbelScan.storeLit, arun, astep,
        initialAState, AState.writeReg, AState.writeArr, initialState,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
        hlo1, hhi1,
        show 1 % M = 1 by decide]
  | succ k ih =>
      intro hk
      have hidx : k < c.loopCount := by omega
      have hword := rawPrefix_wordInv c hc k (Nat.le_of_lt hidx)
      have hlo := rawStep_arr_high c hc k hidx (rawPrefix c k) hword
        (tableLo c) (by simp [Cfg.arrayLen, tableLo])
      have hhi := rawStep_arr_high c hc k hidx (rawPrefix c k) hword
        (tableHi c) (by simp [Cfg.arrayLen, tableHi]; omega)
      rw [← rawPrefix_succ] at hlo hhi
      have hprod := tsel_store_product_le c hc.base k hidx
      have hlohi : tableLo c ≠
          tableHi c + (c.tsel k).isF * (c.tsel k).X := by
        simp [tableLo, tableHi]
        omega
      have hhilo : tableHi c ≠
          tableLo c + (c.tsel k).isF * (c.tsel k).X := by
        simp [tableLo, tableHi]
        omega
      have hprev := ih (Nat.le_of_lt hidx)
      by_cases hz : (c.tsel k).isF * (c.tsel k).X = 0
      · have hF0 : (c.tsel k).isF = 0 := by
          have hFle :=
            LeanCompCert.Ports.Section413G1Denote.tsel_isF_le_one c k
          rcases (by omega : (c.tsel k).isF = 0 ∨
              (c.tsel k).isF = 1) with h | h
          · exact h
          · have hX := tsel_X_pos_of_isF_one c hc k hidx h
            rw [h] at hz
            omega
        have hplanes : tableLo c ≠ tableHi c := by
          simp [tableLo, tableHi]
          omega
        simp only [hF0, Nat.zero_mul, Nat.zero_mod, Nat.add_zero] at hlo hhi
        exact ⟨by simpa [hplanes] using hlo, by simpa [hplanes] using hhi⟩
      · have hloeq : tableLo c ≠
            tableLo c + (c.tsel k).isF * (c.tsel k).X := by omega
        have hhieq : tableHi c ≠
            tableHi c + (c.tsel k).isF * (c.tsel k).X := by omega
        simp only [hlohi, hhilo, hloeq, hhieq, if_false] at hlo hhi
        exact ⟨hlo.trans hprev.1, hhi.trans hprev.2⟩

theorem rawFinal_zero_cells (c : Cfg) (hc : TableAdmissible c) :
    (rawFinal c).arr (tableLo c) = 0 ∧
      (rawFinal c).arr (tableHi c) = 0 := by
  rw [rawFinal_eq_prefix]
  exact rawPrefix_zero_cells c hc c.loopCount (Nat.le_refl _)

theorem final_index_succ (c : Cfg) (X : Nat) (hX : 1 ≤ X) :
    c.phase1 + (X - 1) * c.p + (2 * c.s + 1) + 1 =
      c.phase1 + X * c.p := by
  have hXm : X - 1 + 1 = X := Nat.sub_add_cancel hX
  have hp : 2 * c.s + 1 + 1 = c.p := by
    unfold Cfg.p
    omega
  calc
    c.phase1 + (X - 1) * c.p + (2 * c.s + 1) + 1 =
        c.phase1 + (X - 1) * c.p + c.p := by omega
    _ = c.phase1 + ((X - 1) + 1) * c.p := by rw [Nat.add_mul]; omega
    _ = c.phase1 + X * c.p := by rw [hXm]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem rawPrefix_boundary_cell (c : Cfg) (hc : TableAdmissible c)
    (hsound : LeanCompCert.Ports.Section413G1Sound.Admissible c)
    (X : Nat) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    (rawPrefix c (c.phase1 + X * c.p)).arr (tableLo c + X) =
        (LeanCompCert.Ports.Section413G1Sound.tRunUpto c
          (c.phase1 + X * c.p)).gLo ∧
    (rawPrefix c (c.phase1 + X * c.p)).arr (tableHi c + X) =
        (LeanCompCert.Ports.Section413G1Sound.tRunUpto c
          (c.phase1 + X * c.p)).gHi := by
  let idx := c.phase1 + (X - 1) * c.p + (2 * c.s + 1)
  have hXm1 : X - 1 < c.cap := by omega
  have hz0 := LeanCompCert.Ports.Section413G1Sound.tsel_final_block
    c hsound (X - 1) hXm1
  have hzF : (c.tsel idx).isF = 1 := by
    simpa only [idx] using hz0.2.2.2.1
  have hzX : (c.tsel idx).X = X := by
    have := hz0.2.2.1
    simpa only [idx, Nat.sub_add_cancel hX] using this
  have ht : idx + 1 = c.phase1 + X * c.p := by
    simpa only [idx] using final_index_succ c X hX
  have hbound : idx + 1 ≤ c.loopCount := by
    rw [ht]
    simp only [Cfg.loopCount]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right c.p hXc) c.phase1
  have hidx : idx < c.loopCount := by omega
  have htime := final_index_succ c X hX
  have hword := rawPrefix_wordInv c hc idx (by omega)
  have hlo := rawStep_arr_high c hc idx hidx (rawPrefix c idx) hword
    (tableLo c + X) (by simp [Cfg.arrayLen, tableLo])
  have hhi := rawStep_arr_high c hc idx hidx (rawPrefix c idx) hword
    (tableHi c + X) (by simp [Cfg.arrayLen, tableHi]; omega)
  rw [← rawPrefix_succ] at hlo hhi
  rw [htime] at hlo hhi
  simp only [hzF, hzX, Nat.one_mul] at hlo hhi
  have hbaseplanes : tableLo c ≠ tableHi c := by
    simp [tableLo, tableHi]
    omega
  simp [hbaseplanes] at hlo hhi
  let p := arun idx (rawPrefix c idx) c.body
  have hsel := body_selector c hc.base idx hidx (rawPrefix c idx)
  dsimp only at hsel
  have hpProd : p.regs 35 * p.regs 31 ≤ c.cap := by
    rw [hsel.1, hsel.2]
    exact tsel_store_product_le c hc.base idx hidx
  have hstore := tableStore_core c hc idx p hpProd
  have hp12 : p.regs 12 = (rawPrefix c (c.phase1 + X * c.p)).regs 12 := by
    rw [← htime, rawPrefix_succ, rawStep, arun_append]
    exact (hstore.1 12 (by decide)).symm
  have hp13 : p.regs 13 = (rawPrefix c (c.phase1 + X * c.p)).regs 13 := by
    rw [← htime, rawPrefix_succ, rawStep, arun_append]
    exact (hstore.1 13 (by decide)).symm
  have hreg := (parallel_prefix c hc (c.phase1 + X * c.p) (by
    simp only [Cfg.loopCount]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right c.p hXc) c.phase1)).1.1
  have hobs := basePrefix_obs c hc (c.phase1 + X * c.p) (by
    simp only [Cfg.loopCount]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right c.p hXc) c.phase1)
  have hr12 := hreg 12 (by decide)
  have hr13 := hreg 13 (by decide)
  change (rawPrefix c (c.phase1 + X * c.p)).regs 12 = _ at hr12
  change (rawPrefix c (c.phase1 + X * c.p)).regs 13 = _ at hr13
  have h12M := (rawPrefix_wordInv c hc (c.phase1 + X * c.p) (by
    simp only [Cfg.loopCount]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right c.p hXc) c.phase1)).1 12
  have h13M := (rawPrefix_wordInv c hc (c.phase1 + X * c.p) (by
    simp only [Cfg.loopCount]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right c.p hXc) c.phase1)).1 13
  refine ⟨?_, ?_⟩
  · rw [hlo, show (arun idx (rawPrefix c idx) c.body).regs 12 = p.regs 12 from rfl,
      hp12, Nat.mod_eq_of_lt h12M, hr12]
    exact congrArg TState.gLo hobs
  · rw [hhi, show (arun idx (rawPrefix c idx) c.body).regs 13 = p.regs 13 from rfl,
      hp13, Nat.mod_eq_of_lt h13M, hr13]
    exact congrArg TState.gHi hobs

theorem tsel_store_ne_later (c : Cfg)
    (hc : LeanCompCert.Ports.Section413G1Denote.Admissible c)
    (X idx : Nat) (hX : 1 ≤ X)
    (hstart : c.phase1 + X * c.p ≤ idx) (hidx : idx < c.loopCount) :
    (c.tsel idx).isF * (c.tsel idx).X ≠ X := by
  have hF := LeanCompCert.Ports.Section413G1Denote.tsel_isF_le_one c idx
  rcases (by omega : (c.tsel idx).isF = 0 ∨ (c.tsel idx).isF = 1) with hF0 | hF1
  · rw [hF0, Nat.zero_mul]
    omega
  · rw [hF1, Nat.one_mul]
    have hphase : c.phase1 ≤ idx := by omega
    have hidxM : idx < M := Nat.lt_trans hidx hc.loopLt
    have hphaseM : c.phase1 < M :=
      Nat.lt_of_le_of_lt (by simp [Cfg.loopCount]) hc.loopLt
    have hsubM : idx - c.phase1 < M := by omega
    have hsub : tsub idx c.phase1 = idx - c.phase1 := by
      rw [tsub]
      have heq : idx + (M - c.phase1) = (idx - c.phase1) + M := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hsubM]
    have hpPos : 0 < c.p := LeanCompCert.Ports.Section413G1Denote.p_pos c
    have hxLower : X ≤ (idx - c.phase1) / c.p := by
      apply (Nat.le_div_iff_mul_le hpPos).2
      omega
    have htail : idx - c.phase1 < c.cap * c.p := by
      simp only [Cfg.loopCount] at hidx
      omega
    have hx0 : (idx - c.phase1) / c.p < c.cap :=
      (Nat.div_lt_iff_lt_mul hpPos).2 htail
    have hcapM : c.cap < M := by
      have := hc.arrayLt
      simp [Cfg.arrayLen] at this
      omega
    have hxM : (idx - c.phase1) / c.p + 1 < M := by omega
    have hzX : (c.tsel idx).X = (idx - c.phase1) / c.p + 1 := by
      simp only [Cfg.tsel, hsub, Nat.mod_eq_of_lt hxM]
    rw [hzX]
    omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem rawPrefix_preserves_cell_after (c : Cfg) (hc : TableAdmissible c)
    (X : Nat) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    ∀ d, c.phase1 + X * c.p + d ≤ c.loopCount →
      (rawPrefix c (c.phase1 + X * c.p + d)).arr (tableLo c + X) =
          (rawPrefix c (c.phase1 + X * c.p)).arr (tableLo c + X) ∧
      (rawPrefix c (c.phase1 + X * c.p + d)).arr (tableHi c + X) =
          (rawPrefix c (c.phase1 + X * c.p)).arr (tableHi c + X) := by
  intro d
  induction d with
  | zero => intro hd; simp
  | succ d ih =>
      intro hd
      let idx := c.phase1 + X * c.p + d
      have hidx : idx < c.loopCount := by omega
      have hword := rawPrefix_wordInv c hc idx (Nat.le_of_lt hidx)
      have hlo := rawStep_arr_high c hc idx hidx (rawPrefix c idx) hword
        (tableLo c + X) (by simp [Cfg.arrayLen, tableLo])
      have hhi := rawStep_arr_high c hc idx hidx (rawPrefix c idx) hword
        (tableHi c + X) (by simp [Cfg.arrayLen, tableHi]; omega)
      have hne := tsel_store_ne_later c hc.base X idx hX (by dsimp [idx]; omega) hidx
      have hlohi : tableLo c + X ≠
          tableHi c + (c.tsel idx).isF * (c.tsel idx).X := by
        have hp := tsel_store_product_le c hc.base idx hidx
        simp [tableLo, tableHi]
        omega
      have hhilo : tableHi c + X ≠
          tableLo c + (c.tsel idx).isF * (c.tsel idx).X := by
        have hp := tsel_store_product_le c hc.base idx hidx
        simp [tableLo, tableHi]
        omega
      have hloeq : tableLo c + X ≠
          tableLo c + (c.tsel idx).isF * (c.tsel idx).X := by omega
      have hhieq : tableHi c + X ≠
          tableHi c + (c.tsel idx).isF * (c.tsel idx).X := by omega
      simp only [hlohi, hloeq, hhieq, hhilo, if_false] at hlo hhi
      rw [← rawPrefix_succ] at hlo hhi
      have htime : idx + 1 = c.phase1 + X * c.p + (d + 1) := by
        dsimp [idx]
        omega
      rw [htime] at hlo hhi
      exact ⟨hlo.trans (ih (by omega)).1, hhi.trans (ih (by omega)).2⟩

theorem rawFinal_cell (c : Cfg) (hc : TableAdmissible c)
    (hsound : LeanCompCert.Ports.Section413G1Sound.Admissible c)
    (X : Nat) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    (rawFinal c).arr (tableLo c + X) =
        (LeanCompCert.Ports.Section413G1Sound.tRunUpto c
          (c.phase1 + X * c.p)).gLo ∧
    (rawFinal c).arr (tableHi c + X) =
        (LeanCompCert.Ports.Section413G1Sound.tRunUpto c
          (c.phase1 + X * c.p)).gHi := by
  have hstart : c.phase1 + X * c.p ≤ c.loopCount := by
    simp only [Cfg.loopCount]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right c.p hXc) c.phase1
  have hp := rawPrefix_preserves_cell_after c hc X hX hXc
    (c.loopCount - (c.phase1 + X * c.p)) (by omega)
  rw [Nat.add_sub_of_le hstart] at hp
  rw [rawFinal_eq_prefix]
  exact ⟨hp.1.trans (rawPrefix_boundary_cell c hc hsound X hX hXc).1,
    hp.2.trans (rawPrefix_boundary_cell c hc hsound X hX hXc).2⟩

theorem flagStep_eq_zero_iff {v : Nat} (hv : v < M) (bad : Prop)
    [Decidable bad] : flagStep v bad = 0 ↔ v = 0 ∧ ¬ bad := by
  rw [flagStep, LeanCompCert.Ports.Section413G1Denote.lor_mod_M hv
    (LeanCompCert.Ports.Section413G1Denote.bnat_lt_M bad)]
  constructor
  · intro h
    have hz := LeanCompCert.Ports.Section413G1Sound.or_eq_zero h
    exact ⟨hz.1, LeanCompCert.Ports.Section413G1Sound.bnat_eq_zero_iff.mp hz.2⟩
  · rintro ⟨rfl, hbad⟩
    simp [LeanCompCert.Ports.Section413G1Sound.bnat_false hbad]

theorem flagStep_lt (v : Nat) (bad : Prop) [Decidable bad] :
    flagStep v bad < M := Nat.mod_lt _ (by decide)

theorem checkCellValue_eq_zero_iff {c : Cfg} {expected : Array Cell}
    {arr : Nat → Nat} {v X : Nat} (hv : v < M) :
    checkCellValue c expected arr v X = 0 ↔
      v = 0 ∧
      arr ((tableLo c + X) % M) = encodeZ expected[X]!.lo % M ∧
      arr ((tableHi c + X) % M) = encodeZ expected[X]!.hi % M := by
  unfold checkCellValue
  constructor
  · intro h
    have hout := (flagStep_eq_zero_iff (flagStep_lt _ _) _).mp h
    have hin := (flagStep_eq_zero_iff hv _).mp hout.1
    have hlo : arr ((tableLo c + X) % M) = encodeZ expected[X]!.lo % M :=
      Decidable.not_not.mp hin.2
    have hhi : arr ((tableHi c + X) % M) = encodeZ expected[X]!.hi % M :=
      Decidable.not_not.mp hout.2
    exact ⟨hin.1, hlo, hhi⟩
  · rintro ⟨rfl, hlo, hhi⟩
    apply (flagStep_eq_zero_iff (flagStep_lt _ _) _).mpr
    constructor
    · apply (flagStep_eq_zero_iff hv _).mpr
      exact ⟨rfl, fun h => h hlo⟩
    · exact fun h => h hhi

theorem checkListValue_zero {c : Cfg} {expected : Array Cell}
    {arr : Nat → Nat} : ∀ (xs : List Nat) (v : Nat), v < M →
    xs.foldl (fun v i => checkCellValue c expected arr v (i + 1)) v = 0 →
      v = 0 ∧ ∀ i ∈ xs,
        arr ((tableLo c + (i + 1)) % M) = encodeZ expected[i + 1]!.lo % M ∧
        arr ((tableHi c + (i + 1)) % M) = encodeZ expected[i + 1]!.hi % M := by
  intro xs
  induction xs with
  | nil => intro v hv h; exact ⟨h, by simp⟩
  | cons i rest ih =>
      intro v hv h
      have ht := ih (checkCellValue c expected arr v (i + 1))
        (flagStep_lt _ _) h
      have hcell := (checkCellValue_eq_zero_iff hv).mp ht.1
      refine ⟨hcell.1, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hcell.2
      · exact ht.2 j hj

theorem rawValue_zero_table (c : Cfg) (expected : Array Cell)
    (hc : TableAdmissible c)
    (hzero : rawValue c expected = 0) :
    (rawFinal c).regs rViol = 0 ∧
    ∀ X, 1 ≤ X → X ≤ c.cap →
      (rawFinal c).arr ((tableLo c + X) % M) = encodeZ expected[X]!.lo % M ∧
      (rawFinal c).arr ((tableHi c + X) % M) = encodeZ expected[X]!.hi % M := by
  have hv : (rawFinal c).regs rViol < M := by
    rw [rawFinal_eq_prefix]
    exact (rawPrefix_wordInv c hc c.loopCount (Nat.le_refl _)).1 rViol
  unfold rawValue checkTableValue at hzero
  have hs := checkListValue_zero (List.range c.cap)
    ((rawFinal c).regs rViol) hv hzero
  refine ⟨hs.1, ?_⟩
  intro X hX hXc
  have hm : X - 1 ∈ List.range c.cap := List.mem_range.mpr (by omega)
  have hx := hs.2 (X - 1) hm
  simpa only [Nat.sub_add_cancel hX] using hx

def ExpectedCanonical (c : Cfg) (expected : Array Cell) : Prop :=
  ∀ X, 1 ≤ X → X ≤ c.cap →
    LeanCompCert.Ports.Section413Cells.decodeZ (encodeZ expected[X]!.lo) =
        expected[X]!.lo ∧
      LeanCompCert.Ports.Section413Cells.decodeZ (encodeZ expected[X]!.hi) =
        expected[X]!.hi

theorem cellsOfWords_canonical (c : Cfg) (words : Array (UInt64 × UInt64)) :
    ExpectedCanonical c (cellsOfWords words) := by
  intro X hX hXc
  by_cases hx : X < words.size
  · have hcell : (cellsOfWords words)[X]! =
        ⟨LeanCompCert.Ports.Section413Cells.decodeZ words[X]!.1.toNat,
         LeanCompCert.Ports.Section413Cells.decodeZ words[X]!.2.toNat⟩ := by
      simp [cellsOfWords, getElem!_pos, hx]
    rw [hcell]
    constructor
    · rw [LeanCompCert.Ports.Section413G1Sound.encodeZ_decodeZ_self]
      simpa only [M] using UInt64.toNat_lt words[X]!.1
    · rw [LeanCompCert.Ports.Section413G1Sound.encodeZ_decodeZ_self]
      simpa only [M] using UInt64.toNat_lt words[X]!.2
  · have hcell : (cellsOfWords words)[X]! = default := by
      simp [cellsOfWords, getElem!_neg, hx]
    rw [hcell]
    simp [default,
      LeanCompCert.Ports.Section413Cells.encodeZ,
      LeanCompCert.Ports.Section413Cells.decodeZ,
      LeanCompCert.Ports.Section413Cells.H63,
      LeanCompCert.Verified.MulWide.B64]

theorem rawValue_zero_expected_g1 (c : Cfg) (expected : Array Cell)
    (hc : TableAdmissible c)
    (hsound : LeanCompCert.Ports.Section413G1Sound.Admissible c)
    (hcanonical : ExpectedCanonical c expected)
    (hzero : rawValue c expected = 0) :
    c.tFlag = 0 ∧ ∀ X, 1 ≤ X → X ≤ c.cap →
      expected[X]! =
        (LeanCompCert.Ports.Section413G1Sound.g1Prefix
          c.rounds c.checkLo c.cap X).g := by
  have htab := rawValue_zero_table c expected hc hzero
  have hcore := rawFinal_core_tRun c hc
  have hflag : c.tFlag = 0 := hcore.1.symm.trans htab.1
  refine ⟨hflag, ?_⟩
  intro X hX hXc
  have hcmp := htab.2 X hX hXc
  have hraw := rawFinal_cell c hc hsound X hX hXc
  have hloAddr : tableLo c + X < M := by
    exact Nat.lt_trans (by simp [tableLo, tableArrayLen]; omega) hc.tableLt
  have hhiAddr : tableHi c + X < M := by
    exact Nat.lt_trans (by simp [tableHi, tableArrayLen]; omega) hc.tableLt
  have hloEnc := LeanCompCert.Ports.Section413G1Sound.encodeZ_lt_M expected[X]!.lo
  have hhiEnc := LeanCompCert.Ports.Section413G1Sound.encodeZ_lt_M expected[X]!.hi
  rw [Nat.mod_eq_of_lt hloAddr, Nat.mod_eq_of_lt hloEnc] at hcmp
  rw [Nat.mod_eq_of_lt hhiAddr, Nat.mod_eq_of_lt hhiEnc] at hcmp
  have htlo :
      (LeanCompCert.Ports.Section413G1Sound.tRunUpto c
        (c.phase1 + X * c.p)).gLo = encodeZ expected[X]!.lo :=
    hraw.1.symm.trans hcmp.1
  have hthi :
      (LeanCompCert.Ports.Section413G1Sound.tRunUpto c
        (c.phase1 + X * c.p)).gHi = encodeZ expected[X]!.hi :=
    hraw.2.symm.trans hcmp.2
  have hrel := LeanCompCert.Ports.Section413G1Sound.sweep_prefix
    c hsound hflag X hXc
  have hdecode := hcanonical X hX hXc
  apply (Cell.mk.injEq _ _ _ _).mpr
  constructor
  · have hg := congrArg Cell.lo hrel.g_eq
    rw [htlo, hdecode.1] at hg
    change expected[X]!.lo =
      (LeanCompCert.Ports.Section413G1Sound.g1Prefix
        c.rounds c.checkLo c.cap X).g.lo
    exact hg
  · have hg := congrArg Cell.hi hrel.g_eq
    rw [hthi, hdecode.2] at hg
    change expected[X]!.hi =
      (LeanCompCert.Ports.Section413G1Sound.g1Prefix
        c.rounds c.checkLo c.cap X).g.hi
    exact hg

theorem compiled_zero_expected_g1 (c : Cfg) (expected : Array Cell)
    (hc : TableAdmissible c)
    (hsound : LeanCompCert.Ports.Section413G1Sound.Admissible c)
    (hcanonical : ExpectedCanonical c expected)
    (base : Int) (hBase : BaseOk (tableProgram c expected).arrayLen base)
    (hzero :
      Option.bind
          (Verified.MemFragment.evalMCCSequence
            ((tableProgram c expected).initialMCC base)
            (tableProgram c expected).compile)
          (fun m : Verified.MemFragment.MCCState =>
            m.env ⟨(tableProgram c expected).output + 1⟩) = some 0) :
    c.tFlag = 0 ∧ ∀ X, 1 ≤ X → X ≤ c.cap →
      expected[X]! =
        (LeanCompCert.Ports.Section413G1Sound.g1Prefix
          c.rounds c.checkLo c.cap X).g := by
  have hden := tableProgram_denote c expected hc
  have hrun := tableProgram_compiled c expected base hBase (rawValue c expected) hden
  rw [hzero] at hrun
  have hzInt : ((rawValue c expected : Nat) : Int) = 0 :=
    (Option.some.inj hrun).symm
  have hz : rawValue c expected = 0 := by exact_mod_cast hzInt
  exact rawValue_zero_expected_g1 c expected hc hsound hcanonical hz

end LeanCompCert.Ports.Section413G1TableSound

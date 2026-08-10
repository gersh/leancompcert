import LeanCompCert.Ports.CDEMAbelSieveTable

/-! # Emitted initialization for the finite CDEM resident sieve -/

namespace LeanCompCert.Ports.CDEMAbelSieveInit

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveTelescope
open LeanCompCert.Ports.CDEMAbelSieveReady
open LeanCompCert.Ports.CDEMAbelSieveTable

theorem cdem_storeLit_arr (idx cell value j : Nat) (s : AState)
    (hcell : cell < M) (hvalue : value < M) :
    (arun idx s (storeLit cell value)).arr j =
      if j = cell then value else s.arr j := by
  simp [storeLit, arun, astep, AState.writeReg, AState.writeArr,
    InstrBlock.sdest, InstrBlock.sval, denoteOperand,
    Nat.mod_eq_of_lt hcell, Nat.mod_eq_of_lt hvalue]

theorem cdem_storeLits_arr (idx j : Nat) (s : AState)
    (l : List (Nat × Nat)) (hword : ∀ x ∈ l, x.1 < M ∧ x.2 < M) :
    (arun idx s (storeLits l)).arr j =
      l.foldl (fun old x => if j = x.1 then x.2 else old) (s.arr j) := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append, List.foldl_cons]
      change (arun idx (arun idx s (storeLit x.1 x.2))
        (storeLits xs)).arr j = _
      rw [ih (arun idx s (storeLit x.1 x.2))
        (fun y hy => hword y (by simp [hy]))]
      rw [cdem_storeLit_arr idx x.1 x.2 j s
        (hword x (by simp)).1 (hword x (by simp)).2]

theorem cdem_cellWrite_of_forall_ne (j init : Nat)
    (l : List (Nat × Nat)) (hne : ∀ x ∈ l, x.1 ≠ j) :
    l.foldl (fun old x => if j = x.1 then x.2 else old) init = init := by
  induction l generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [if_neg (fun h => hne x (by simp) h.symm)]
      exact ih init (fun y hy => hne y (by simp [hy]))

theorem cdem_cellWrite_eq_of_mem (j value init : Nat)
    (l : List (Nat × Nat)) (hmem : (j, value) ∈ l)
    (hvalue : ∀ x ∈ l, x.1 = j → x.2 = value) :
    l.foldl (fun old x => if j = x.1 then x.2 else old) init = value := by
  induction l generalizing init with
  | nil => simp at hmem
  | cons x xs ih =>
      simp only [List.foldl_cons]
      by_cases hx : x.1 = j
      · have hxv : x.2 = value := hvalue x (by simp) hx
        rw [if_pos hx.symm, hxv]
        by_cases htail : (j, value) ∈ xs
        · exact ih value htail (fun y hy => hvalue y (by simp [hy]))
        · apply cdem_cellWrite_of_forall_ne
          intro y hy hyj
          have hyv : y.2 = value := hvalue y (by simp [hy]) hyj
          apply htail
          cases y
          simp_all
      · rw [if_neg (fun h => hx h.symm)]
        have htail : (j, value) ∈ xs := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst x
            exact (hx rfl).elim
          · exact htail
        exact ih init htail (fun y hy => hvalue y (by simp [hy]))

theorem cdem_seedRegs_arr (idx : Nat) (s : AState)
    (l : List (Nat × Nat)) :
    (arun idx s (seedRegs l)).arr = s.arr := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [seedRegs, List.map_cons, arun]
      exact ih _

theorem cdem_seedReg_reg (idx r : Nat) (s : AState) (x : Nat × Nat) :
    (arun idx s [.scalar (.mov x.1 (.lit x.2))]).regs r =
      if r = x.1 then x.2 % M else s.regs r := by
  simp [arun, astep, AState.writeReg, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand]

theorem cdem_seedRegs_reg_zero (idx r : Nat) (s : AState)
    (l : List (Nat × Nat)) (hs : s.regs r = 0)
    (hz : ∀ x ∈ l, x.1 = r → x.2 = 0) :
    (arun idx s (seedRegs l)).regs r = 0 := by
  induction l generalizing s with
  | nil => exact hs
  | cons x xs ih =>
      simp only [seedRegs, List.map_cons, arun]
      apply ih (arun idx s [.scalar (.mov x.1 (.lit x.2))])
      · rw [cdem_seedReg_reg]
        by_cases hxr : x.1 = r
        · rw [if_pos hxr.symm, hz x (by simp) hxr, Nat.zero_mod]
        · rw [if_neg (fun h => hxr h.symm), hs]
      · intro y hy
        exact hz y (by simp [hy])

theorem cdem_storeLit_regs_frame (idx cell value r : Nat) (s : AState)
    (hr240 : r ≠ 240) (hr241 : r ≠ 241) :
    (arun idx s (storeLit cell value)).regs r = s.regs r := by
  simp [storeLit, arun, astep, AState.writeReg, AState.writeArr,
    InstrBlock.sdest, InstrBlock.sval, denoteOperand, hr240, hr241]

theorem cdem_storeLits_regs_frame (idx r : Nat) (s : AState)
    (l : List (Nat × Nat)) (hr240 : r ≠ 240) (hr241 : r ≠ 241) :
    (arun idx s (storeLits l)).regs r = s.regs r := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [storeLits, List.flatMap_cons, arun_append]
      change (arun idx (arun idx s (storeLit x.1 x.2))
        (storeLits xs)).regs r = _
      rw [ih, cdem_storeLit_regs_frame idx x.1 x.2 r s hr240 hr241]

theorem primeCells_word (c : Cfg) (hpnM : c.pn < M)
    (hprimeM : ∀ p ∈ c.primes, p < M) :
    ∀ x ∈ c.primeCells, x.1 < M ∧ x.2 < M := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨row, hrow, rfl⟩
  have hi := List.mem_zipIdx' hrow
  constructor
  · unfold Cfg.primeBase
    simpa [Cfg.pn] using Nat.lt_trans hi.1 hpnM
  · exact hprimeM row.1 (List.fst_mem_of_mem_zipIdx hrow)

theorem primeCell_mem (c : Cfg) (j : Nat) (hj : j < c.pn) :
    (j, c.primes[j]) ∈ c.primeCells := by
  apply List.mem_map.mpr
  refine ⟨(c.primes[j], j), ?_, ?_⟩
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simp)
  · simp [Cfg.primeBase]

theorem primeCells_value (c : Cfg) (j : Nat) (hj : j < c.pn)
    (x : Nat × Nat) (hx : x ∈ c.primeCells) (haddr : x.1 = j) :
    x.2 = c.primes[j] := by
  rcases List.mem_map.mp hx with ⟨row, hrow, rfl⟩
  have hi := List.mem_zipIdx' hrow
  dsimp only at haddr ⊢
  subst j
  simpa [Cfg.primeBase] using hi.2

def sieveEntry (c : Cfg) : AState :=
  arun 0 initialAState c.init

theorem sieveEntry_prime (c : Cfg) (hpnM : c.pn < M)
    (hprimeM : ∀ p ∈ c.primes, p < M) (j : Nat) (hj : j < c.pn) :
    (sieveEntry c).arr j = c.primes[j] := by
  unfold sieveEntry Cfg.init
  rw [arun_append]
  rw [show (arun 0 (arun 0 initialAState (storeLits c.primeCells))
      (seedRegs c.seedList)).arr =
      (arun 0 initialAState (storeLits c.primeCells)).arr from
    cdem_seedRegs_arr 0 _ _]
  rw [cdem_storeLits_arr 0 j initialAState c.primeCells
    (primeCells_word c hpnM hprimeM)]
  exact cdem_cellWrite_eq_of_mem j c.primes[j] 0 c.primeCells
    (primeCell_mem c j hj) (primeCells_value c j hj)

theorem sieveEntry_seed (c : Cfg) :
    (sieveEntry c).regs rZero = 0 ∧
    (sieveEntry c).regs rN = 0 ∧
    (sieveEntry c).regs rPj = 0 ∧
    (sieveEntry c).regs rM = 0 ∧
    (sieveEntry c).regs rPar = 0 ∧
    (sieveEntry c).regs rSqf = 0 := by
  unfold sieveEntry Cfg.init
  rw [arun_append]
  have frame (r : Nat) (hr240 : r ≠ 240) (hr241 : r ≠ 241) :
      (arun 0 initialAState (storeLits c.primeCells)).regs r = 0 := by
    rw [cdem_storeLits_regs_frame 0 r initialAState c.primeCells hr240 hr241]
    rfl
  have seededZero (r : Nat) (hr240 : r ≠ 240) (hr241 : r ≠ 241)
      (hz : ∀ x ∈ c.seedList, x.1 = r → x.2 = 0) :
      (arun 0 (arun 0 initialAState (storeLits c.primeCells))
        (seedRegs c.seedList)).regs r = 0 :=
    cdem_seedRegs_reg_zero 0 r _ c.seedList
      (frame r hr240 hr241) hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply seededZero rZero (by decide) (by decide)
    simp [Cfg.seedList, rZero, rW, rD, rSl, rSh, rT, rT2, rK]
  · apply seededZero rN (by decide) (by decide)
    simp [Cfg.seedList, rN, rW, rD, rSl, rSh, rT, rT2, rK]
  · apply seededZero rPj (by decide) (by decide)
    simp [Cfg.seedList, rPj, rW, rD, rSl, rSh, rT, rT2, rK]
  · apply seededZero rM (by decide) (by decide)
    simp [Cfg.seedList, rM, rW, rD, rSl, rSh, rT, rT2, rK]
  · apply seededZero rPar (by decide) (by decide)
    simp [Cfg.seedList, rPar, rW, rD, rSl, rSh, rT, rT2, rK]
  · apply seededZero rSqf (by decide) (by decide)
    simp [Cfg.seedList, rSqf, rW, rD, rSl, rSh, rT, rT2, rK]

theorem selectors_sieve_run (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hidx : idx < c.sieveLen) :
    let out := arun idx st c.selectors
    out.regs 40 = 1 ∧ out.regs 41 = 0 ∧ out.regs 42 = 0 ∧
      out.regs 43 = 0 ∧ out.arr = st.arr := by
  have hidxMod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hsieveMod : c.sieveLen % M = c.sieveLen :=
    Nat.mod_eq_of_lt hsieveM
  have hwrap0 : (1 + (M - 1)) % M = 0 := by decide
  simp [Cfg.selectors, arun, astep, InstrBlock.sdest, InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rR, hidxMod, hsieveMod,
    hidx, hwrap0]

def initialSieveModel (c : Cfg) : SieveState :=
  { arr := (sieveEntry c).arr
    n := 0, pj := 0, m := 0, par := 0, sqf := 0 }

def sieveSelected (c : Cfg) : AState :=
  arun 0 (sieveEntry c) c.selectors

theorem sieveEntry_word (c : Cfg) :
    (∀ j, (sieveEntry c).regs j < M) ∧
      (∀ j, (sieveEntry c).arr j < M) := by
  have hstores := arun_word 0 (storeLits c.primeCells) initialAState
    (by intro j; simp [initialAState, initialState, M])
    (by intro j; simp [initialAState, M])
  have hseeded := arun_word 0 (seedRegs c.seedList)
    (arun 0 initialAState (storeLits c.primeCells)) hstores.1 hstores.2
  unfold sieveEntry Cfg.init
  rw [arun_append]
  exact hseeded

theorem sieveSelected_rep (c : Cfg) (hsievePos : 0 < c.sieveLen)
    (hsieveM : c.sieveLen < M) :
    SieveStateRep (initialSieveModel c) (sieveSelected c) := by
  have hsel := selectors_sieve_run c 0 (sieveEntry c) (by decide)
    hsieveM hsievePos
  have hseed := sieveEntry_seed c
  have frame (r : Nat) (hwrites : ArrayRegFrame.writes r c.selectors = false) :
      (sieveSelected c).regs r = (sieveEntry c).regs r := by
    exact ArrayRegFrame.arun_frame 0 r c.selectors hwrites (sieveEntry c)
  have hword := arun_word 0 c.selectors (sieveEntry c)
    (sieveEntry_word c).1 (sieveEntry_word c).2
  refine
    { arr := by exact hsel.2.2.2.2.symm
      n := by simpa [initialSieveModel] using
        (frame rN (by rfl)).trans hseed.2.1
      pj := by simpa [initialSieveModel] using
        (frame rPj (by rfl)).trans hseed.2.2.1
      m := by simpa [initialSieveModel] using
        (frame rM (by rfl)).trans hseed.2.2.2.1
      par := by simpa [initialSieveModel] using
        (frame rPar (by rfl)).trans hseed.2.2.2.2.1
      sqf := by simpa [initialSieveModel] using
        (frame rSqf (by rfl)).trans hseed.2.2.2.2.2
      gate := hsel.1
      zero := (frame rZero (by rfl)).trans hseed.1
      regsWord := hword.1
      arrWord := hword.2 }

theorem initialSieveModel_cursor (c : Cfg) (hpnPos : 0 < c.pn)
    (hprimePos : ∀ p ∈ c.primes, 0 < p) (hpnM : c.pn < M)
    (hprimeM : ∀ p ∈ c.primes, p < M) :
    SieveCursorInv c (initialSieveModel c) := by
  refine
    { pjBound := by simpa [initialSieveModel] using hpnPos
      primePos := ?_ }
  intro j hj
  rw [show (initialSieveModel c).arr j = (sieveEntry c).arr j by rfl,
    sieveEntry_prime c hpnM hprimeM j hj]
  exact hprimePos c.primes[j] (List.getElem_mem hj)

theorem initialSieveModel_table (c : Cfg) (hpnM : c.pn < M)
    (hprimeM : ∀ p ∈ c.primes, p < M) :
    SieveTableInv c (initialSieveModel c) := by
  apply sieve_table_zero c (initialSieveModel c) (by rfl) (by rfl)
  · intro j hj
    exact sieveEntry_prime c hpnM hprimeM j hj
  · simp [initialSieveModel, M]
  · simp [initialSieveModel, M]
  · simp [initialSieveModel, M]

theorem initialized_sieve_machine_full_muCodeFor (c : Cfg)
    (hpnPos : 0 < c.pn) (hpnM : c.pn < M)
    (hsievePos : 0 < c.sieveLen) (hsieveM : c.sieveLen < M)
    (hsinkM : c.sink < M) (hprimePos : ∀ p ∈ c.primes, 0 < p)
    (hprimeM : ∀ p ∈ c.primes, p < M)
    (hprimes : c.primes =
      LeanCompCert.Ports.ArraySegSieve.primesBelow (Nat.sqrt c.kBound + 1)) :
    let out := sieveIter c 0 c.sieveLen (sieveSelected c)
    ∀ d, d < c.k1 →
      out.arr (d + c.muBase) = Ref.muCodeFor c.kBound d := by
  apply sieve_machine_full_muCodeFor c 0 (sieveSelected c)
    (initialSieveModel c)
  · exact sieveSelected_rep c hsievePos hsieveM
  · exact initialSieveModel_cursor c hpnPos hprimePos hpnM hprimeM
  · rfl
  · rfl
  · exact initialSieveModel_table c hpnM hprimeM
  · exact hpnM
  · exact hsinkM
  · exact hprimes

end LeanCompCert.Ports.CDEMAbelSieveInit

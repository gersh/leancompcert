import LeanCompCert.Ports.CDEMAbelSieveSource

/-! # Resident-table invariant for the finite CDEM Möbius sieve -/

namespace LeanCompCert.Ports.CDEMAbelSieveTable

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSievePrefix
open LeanCompCert.Ports.CDEMAbelSieveTelescope
open LeanCompCert.Ports.CDEMAbelSieveReady
open LeanCompCert.Ports.CDEMAbelSieveSource

theorem sieveFactorFold_take_succ (primes : List Nat) (n j : Nat)
    (hj : j < primes.length) :
    sieveFactorFold (primes.take (j + 1)) n =
      sieveFactorStep (sieveFactorFold (primes.take j) n) primes[j] := by
  rw [List.take_succ_eq_append_getElem hj]
  unfold sieveFactorFold
  rw [List.foldl_append]
  rfl

theorem sieveFactorFold_word (primes : List Nat) (n : Nat) (hn : n < M) :
    let out := sieveFactorFold primes n
    out.m < M ∧ out.par < M ∧ out.sqf < M := by
  have aux : ∀ (ps : List Nat) (s : SieveFactorState),
      s.m < M → s.par < M → s.sqf < M →
        let out := ps.foldl sieveFactorStep s
        out.m < M ∧ out.par < M ∧ out.sqf < M := by
    intro ps
    induction ps with
    | nil =>
        intro s hm hpar hsqf
        exact ⟨hm, hpar, hsqf⟩
    | cons p ps ih =>
        intro s hm hpar hsqf
        simp only [List.foldl_cons]
        have hs := sieveFactorStep_word s p hm
        exact ih _ hs.1 hs.2.1 hs.2.2
  simpa [sieveFactorFold] using
    (aux primes ⟨n, 0, 1⟩ hn
      (show (0 : Nat) < M by decide) (show (1 : Nat) < M by decide))

/-- Pure source invariant carried by the finite sieve cursor.  The table
statement is deliberately about the finite emitted prime list; identifying
that list with the production `muCodeFor` input is a separate rewrite. -/
structure SieveTableInv (c : Cfg) (s : SieveState) : Prop where
  primeCells : ∀ j, (hj : j < c.pn) → s.arr j = c.primes[j]
  completed : ∀ d, d < s.n →
    s.arr (d + c.muBase) = Ref.muCodeWith c.primes d
  carry : s.pj ≠ 0 →
    ⟨s.m, s.par, s.sqf⟩ = sieveFactorFold (c.primes.take s.pj) s.n
  nBound : s.n ≤ c.k1
  nWord : s.n < M
  mWord : s.m < M
  parWord : s.par < M
  sqfWord : s.sqf < M

theorem sieveRow_eq_primePrefixSucc (c : Cfg) (s : SieveState)
    (h : SieveTableInv c s) (hpj : s.pj < c.pn) :
    s.row = sieveFactorFold (c.primes.take (s.pj + 1)) s.n := by
  have hp := h.primeCells s.pj hpj
  have hstep := sieveFactorFold_take_succ c.primes s.n s.pj hpj
  by_cases hzero : s.pj = 0
  · rw [sieveRow_zero s hzero]
    simp only [hzero] at hp hstep
    rw [hp]
    simpa [hzero, sieveFactorFold] using hstep.symm
  · rw [sieveRow_nonzero s hzero h.parWord h.sqfWord, h.carry hzero,
      hp, hstep]

theorem sieveRow_word (c : Cfg) (s : SieveState)
    (h : SieveTableInv c s) (hpj : s.pj < c.pn) :
    s.row.m < M ∧ s.row.par < M ∧ s.row.sqf < M := by
  rw [sieveRow_eq_primePrefixSucc c s h hpj]
  exact sieveFactorFold_word _ _ h.nWord

theorem sieve_table_step (c : Cfg) (s : SieveState)
    (h : SieveTableInv c s) (hcursor : SieveCursorInv c s)
    (hn : s.n < c.k1) (hnNextWord : s.n + 1 < M) :
    SieveTableInv c (s.step c) := by
  have hrow := sieveRow_eq_primePrefixSucc c s h hcursor.pjBound
  have hrowWord := sieveRow_word c s h hcursor.pjBound
  by_cases hlast : s.pj = c.pn - 1
  · have hpnPos : 0 < c.pn := Nat.lt_of_le_of_lt (Nat.zero_le _) hcursor.pjBound
    have hpjFull : s.pj + 1 = c.pn := by omega
    have htake : c.primes.take (s.pj + 1) = c.primes := by
      rw [hpjFull]
      simp [Cfg.pn]
    refine
      { primeCells := ?_
        completed := ?_
        carry := ?_
        nBound := by simp [SieveState.step, hlast]; omega
        nWord := by simpa [SieveState.step, hlast] using hnNextWord
        mWord := by simpa [SieveState.step, hlast] using hrowWord.1
        parWord := by simpa [SieveState.step, hlast] using hrowWord.2.1
        sqfWord := by simpa [SieveState.step, hlast] using hrowWord.2.2 }
    · intro j hj
      have hne : j ≠ s.n + c.muBase := by
        unfold Cfg.muBase
        omega
      simpa [SieveState.step, hlast, writeCell, hne] using
        h.primeCells j hj
    · intro d hd
      have hd' : d < s.n + 1 := by
        simpa [SieveState.step, hlast] using hd
      by_cases hdn : d = s.n
      · subst d
        have hcode : s.code = Ref.muCodeWith c.primes s.n := by
          unfold SieveState.code
          rw [hrow, htake]
          exact sieveFactorFold_code_source c.primes s.n
        simpa [SieveState.step, hlast, writeCell] using hcode
      · have hdlt : d < s.n := by omega
        simpa [SieveState.step, hlast, writeCell, hdn] using
          h.completed d hdlt
    · intro hpj
      simp [SieveState.step, hlast] at hpj
  · refine
      { primeCells := ?_
        completed := ?_
        carry := ?_
        nBound := by simpa [SieveState.step, hlast] using h.nBound
        nWord := by simpa [SieveState.step, hlast] using h.nWord
        mWord := by simpa [SieveState.step, hlast] using hrowWord.1
        parWord := by simpa [SieveState.step, hlast] using hrowWord.2.1
        sqfWord := by simpa [SieveState.step, hlast] using hrowWord.2.2 }
    · intro j hj
      have hne : j ≠ c.sink := by
        unfold Cfg.sink Cfg.winBase Cfg.muBase
        omega
      simpa [SieveState.step, hlast, writeCell, hne] using
        h.primeCells j hj
    · intro d hd
      have hdlt : d < s.n := by
        simpa [SieveState.step, hlast] using hd
      have hne : d + c.muBase ≠ c.sink := by
        unfold Cfg.sink Cfg.winBase
        omega
      simpa [SieveState.step, hlast, writeCell, hne] using
        h.completed d hdlt
    · intro _
      simpa [SieveState.step, hlast] using hrow

theorem sieve_table_zero (c : Cfg) (s : SieveState)
    (hn : s.n = 0) (hpj : s.pj = 0)
    (hprime : ∀ j, (hj : j < c.pn) → s.arr j = c.primes[j])
    (hm : s.m < M) (hpar : s.par < M) (hsqf : s.sqf < M) :
    SieveTableInv c s := by
  refine
    { primeCells := hprime
      completed := ?_
      carry := ?_
      nBound := by simp [hn]
      nWord := by simp [hn, M]
      mWord := hm
      parWord := hpar
      sqfWord := hsqf }
  · intro d hd
    simp [hn] at hd
  · intro hne
    exact (hne hpj).elim

theorem sieve_iter_n_lt_from_zero (c : Cfg) (s : SieveState)
    (hcursor : SieveCursorInv c s) (hn : s.n = 0) (hpj : s.pj = 0)
    (i : Nat) (hi : i < c.sieveLen) :
    (s.iter c i).n < c.k1 := by
  let t := s.iter c i
  have hrank : sieveRank c t = i :=
    sieve_iter_rank_from_zero c s hcursor hn hpj i
  have hmul : t.n * c.pn < c.k1 * c.pn := by
    calc
      t.n * c.pn ≤ sieveRank c t := by simp [sieveRank]
      _ = i := hrank
      _ < c.sieveLen := hi
      _ = c.k1 * c.pn := rfl
  exact Nat.lt_of_mul_lt_mul_right hmul

theorem sieve_table_iter_from_zero (c : Cfg) (s : SieveState)
    (hcursor : SieveCursorInv c s) (hn : s.n = 0) (hpj : s.pj = 0)
    (htable : SieveTableInv c s) (hpnM : c.pn < M)
    (hsinkM : c.sink < M) (count : Nat) (hcount : count ≤ c.sieveLen) :
    SieveTableInv c (s.iter c count) := by
  induction count with
  | zero => simpa [SieveState.iter] using htable
  | succ count ih =>
      have hcountLt : count < c.sieveLen := by omega
      have hpre := ih (by omega)
      have hready := sieve_iter_ready_from_zero c s hcursor hn hpj hpnM
        hsinkM count hcountLt
      have hstep := sieve_table_step c (s.iter c count) hpre
        (sieve_cursor_iter c s hcursor count)
        (sieve_iter_n_lt_from_zero c s hcursor hn hpj count hcountLt)
        hready.nNextWord
      simpa [SieveState.iter] using hstep

theorem sieve_table_full (c : Cfg) (s : SieveState)
    (hcursor : SieveCursorInv c s) (hn : s.n = 0) (hpj : s.pj = 0)
    (htable : SieveTableInv c s) (hpnM : c.pn < M)
    (hsinkM : c.sink < M) :
    let out := s.iter c c.sieveLen
    ∀ d, d < c.k1 →
      out.arr (d + c.muBase) = Ref.muCodeWith c.primes d := by
  let out := s.iter c c.sieveLen
  have htab := sieve_table_iter_from_zero c s hcursor hn hpj htable hpnM
    hsinkM c.sieveLen (by omega)
  have hcursors := sieve_iter_full_cursors c s hcursor hn hpj
  dsimp only
  intro d hd
  apply htab.completed d
  rw [hcursors.1]
  exact hd

theorem sieve_machine_full_table (c : Cfg) (idx : Nat)
    (machine : LeanCompCert.Verified.ArrayState.AState)
    (model : SieveState) (hrep : SieveStateRep model machine)
    (hcursor : SieveCursorInv c model) (hn : model.n = 0)
    (hpj : model.pj = 0) (htable : SieveTableInv c model)
    (hpnM : c.pn < M) (hsinkM : c.sink < M) :
    let out := sieveIter c idx c.sieveLen machine
    ∀ d, d < c.k1 →
      out.arr (d + c.muBase) = Ref.muCodeWith c.primes d := by
  have href := sieveIter_state_refines_from_zero c idx c.sieveLen machine model
    hrep hcursor hn hpj hpnM hsinkM (by omega)
  have hpure := sieve_table_full c model hcursor hn hpj htable hpnM hsinkM
  dsimp only
  intro d hd
  rw [href.arr]
  exact hpure d hd

theorem sieve_machine_full_muCodeFor (c : Cfg) (idx : Nat)
    (machine : LeanCompCert.Verified.ArrayState.AState)
    (model : SieveState) (hrep : SieveStateRep model machine)
    (hcursor : SieveCursorInv c model) (hn : model.n = 0)
    (hpj : model.pj = 0) (htable : SieveTableInv c model)
    (hpnM : c.pn < M) (hsinkM : c.sink < M)
    (hprimes : c.primes = Ref.muPrimes c.kBound) :
    let out := sieveIter c idx c.sieveLen machine
    ∀ d, d < c.k1 →
      out.arr (d + c.muBase) = Ref.muCodeFor c.kBound d := by
  have hfull := sieve_machine_full_table c idx machine model hrep hcursor hn hpj
    htable hpnM hsinkM
  dsimp only
  intro d hd
  rw [hfull d hd, Ref.muCodeFor, ← hprimes]

end LeanCompCert.Ports.CDEMAbelSieveTable

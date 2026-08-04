import LeanCompCert.Ports.G1215CheckDenote

/-!
# The `G1215Check` program's denotation

The last layer before the certificate side.  `Ports/G1215CheckDenote.lean`
proved `gRun_spec` — one flat round's effect on the carried registers is
exactly `gRound`, and `Inv` is preserved — together with the word chase and
the four `udiv` guards.  This module turns that into a statement about the
whole `Program`:

* `gBody_defined` — the emitted body is defined at every visited index and
  agrees with `gRun` below the temporary cursor;
* `gStep_spec` — the machine step, packaged for the fold bridge;
* `gProgram_denote` — **the program denotes the epilogue-corrected good flag
  of the flat `gRound` fold**, with no fold evaluated, so the theorem costs the
  same at `len = 8` and at `len = 10⁷`;
* `gFold_blocked` — the flat fold is the per-candidate fold of `R`-round
  blocks.

The one structural difference from the sibling `Ports/GFoldCheckRun.lean` §13
is the **epilogue**: `GFoldCheck`'s is empty, while this port re-tests the two
exact final sums there.  `RS62LadderEncoding.Program.denote_eq_foldl_mem`
takes a `fin : RegState → RegState` with an *exact* equality obligation, so
`fin` cannot be `run 0 s (blkEp c)` — the compiled block also writes the
expression compiler's temporaries.  `gEpi` is the actual machine state, its
definedness comes from `Straight.block_correct` (`blkEp` is division-free, so
it never fails), and the same `block_correct` gives `gEpi c s 0 =
run 0 s (blkEp c) 0` because register `0` is below the cursor.

Nothing here evaluates a fold and nothing here is a certificate.
-/

namespace LeanCompCert.Ports.G1215Check

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight

set_option maxRecDepth 8000

/-! ## §10 The body is defined, and agrees with `gRun` below the cursor

`Straight.block_correct` produces a machine state that agrees with `run` only
*below the temporary cursor* — the compiled blocks also write the expression
compiler's temporaries `72, 73, …`, which `run` does not.  Every live register
is below `cursor = 72`, so agreement below the cursor is all the rest needs. -/

section Denote

variable {c : Params} {k : Nat} {s : RegState}

private theorem obindSome {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

private theorem run_nil (k : Nat) (t : RegState) : run k t [] = t := rfl

private theorem divStep_ne' (dest : Nat) (op : Op) (a b j : Nat) (t : RegState)
    (h : j ≠ dest) : divStep dest op a b t j = t j := by
  simp [divStep, RegState.set, h]

private theorem litDivStep_ne (dest v b j : Nat) (t : RegState)
    (h : j ≠ dest) : litDivStep dest v b t j = t j := by
  simp [litDivStep, RegState.set, h]

private theorem divStep_congr (dest : Nat) (op : Op) (a b : Nat)
    (ha : a < cursor) (hb : b < cursor) {u t : RegState}
    (hag : AgreeBelow cursor u t) :
    AgreeBelow cursor (divStep dest op a b u) (divStep dest op a b t) := by
  intro j hj
  by_cases hjd : j = dest
  · subst hjd
    simp [divStep, RegState.set, hag a ha, hag b hb]
  · rw [divStep_ne' _ _ _ _ _ _ hjd, divStep_ne' _ _ _ _ _ _ hjd]
    exact hag j hj

private theorem litDivStep_congr (dest v b : Nat) (hb : b < cursor)
    {u t : RegState} (hag : AgreeBelow cursor u t) :
    AgreeBelow cursor (litDivStep dest v b u) (litDivStep dest v b t) := by
  intro j hj
  by_cases hjd : j = dest
  · subst hjd
    simp [litDivStep, RegState.set, hag b hb]
  · rw [litDivStep_ne _ _ _ _ _ hjd, litDivStep_ne _ _ _ _ _ hjd]
    exact hag j hj

private theorem udivStep_denote (j dest a b : Nat) (u : RegState)
    (hne : u b ≠ 0) :
    denoteInstrs j u [Instr.binop dest Op.udiv (.reg a) (.reg b)] =
      some (divStep dest Op.udiv a b u) := by
  simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, divStep, hne]

private theorem litDivStep_denote (j dest v b : Nat) (u : RegState)
    (hne : u b ≠ 0) :
    denoteInstrs j u [Instr.binop dest Op.udiv (.lit v) (.reg b)] =
      some (litDivStep dest v b u) := by
  simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, litDivStep, hne]

private theorem idxDiv_denote (j R : Nat) (u : RegState) (hne : R % M ≠ 0) :
    denoteInstrs j u
      [Instr.binop 11 Op.udiv .idx (.lit R), Instr.binop 12 Op.urem .idx (.lit R)]
      = some (idxDivStep R j u) := by
  simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, idxDivStep, hne]

private theorem blockStep_agree (j : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) (u t : RegState)
    (hag : AgreeBelow cursor u t) :
    ∃ u', denoteInstrs j u (block cursor as) = some u' ∧
      AgreeBelow cursor u' (run j t as) := by
  obtain ⟨u', h1, h2⟩ := block_correct j cursor as hWF u
  exact ⟨u', h1,
    fun r hr => (h2 r hr).trans (run_congr j cursor as hWF u t hag r hr)⟩

/-- **The body is defined at every visited index, and simulates `gRun`.** -/
theorem gBody_defined (hc : c.Sane) (h14 : st1 c k s 14 ≠ 0)
    (h22 : st3 c k s 22 ≠ 0) (h44 : st5 c k s 44 ≠ 0)
    (h49 : st7 c k s 49 ≠ 0) :
    ∃ s', denoteInstrs k s (gBody c) = some s' ∧
      AgreeBelow cursor s' (gRun c k s) := by
  have hRne : c.R % M ≠ 0 := by
    rw [hc.RModM]
    have := hc.RPos
    omega
  have hsplit : gBody c =
      [Instr.binop 11 .udiv .idx (.lit c.R),
       Instr.binop 12 .urem .idx (.lit c.R)] ++
      (block cursor (blkA c) ++
        ([Instr.binop 19 .udiv (.reg 1) (.reg 14)] ++
          ([Instr.binop 20 .udiv (.reg 19) (.reg 14)] ++
            (block cursor blkB ++
              ([Instr.binop 23 .udiv (.lit (2 ^ 44)) (.reg 22)] ++
                (block cursor blkC ++
                  ([Instr.binop 45 .udiv (.reg 43) (.reg 44)] ++
                    (block cursor blkD ++
                      ([Instr.binop 50 .udiv (.reg 48) (.reg 49)] ++
                        block cursor (blkF c)))))))))) := by
    simp only [gBody, List.append_assoc, List.cons_append, List.nil_append]
  have step1 : denoteInstrs k s
      [Instr.binop 11 .udiv .idx (.lit c.R),
       Instr.binop 12 .urem .idx (.lit c.R)] =
        some (idxDivStep c.R k s) := idxDiv_denote k c.R s hRne
  -- stage A
  obtain ⟨u1, hu1, ha1⟩ := blockStep_agree k (blkA c) (blkA_wf c)
    (idxDivStep c.R k s) (idxDivStep c.R k s)
    (AgreeBelow.refl cursor (idxDivStep c.R k s))
  have hAeq : run k (idxDivStep c.R k s) (blkA c) = st1 c k s := rfl
  have ha1' : AgreeBelow cursor u1 (st1 c k s) := by rw [← hAeq]; exact ha1
  have hne1 : u1 14 ≠ 0 := by rw [ha1' 14 (by decide)]; exact h14
  -- the two peel divisions
  have ha2 : AgreeBelow cursor (divStep 19 Op.udiv 1 14 u1)
      (divStep 19 Op.udiv 1 14 (st1 c k s)) :=
    divStep_congr 19 Op.udiv 1 14 (by decide) (by decide) ha1'
  have hne2 : (divStep 19 Op.udiv 1 14 u1) 14 ≠ 0 := by
    rw [divStep_ne' _ _ _ _ _ _ (by decide)]; exact hne1
  have ha3 : AgreeBelow cursor
      (divStep 20 Op.udiv 19 14 (divStep 19 Op.udiv 1 14 u1)) (st2 c k s) :=
    divStep_congr 20 Op.udiv 19 14 (by decide) (by decide) ha2
  -- stage B
  obtain ⟨u4, hu4, ha4⟩ := blockStep_agree k blkB blkB_wf
    (divStep 20 Op.udiv 19 14 (divStep 19 Op.udiv 1 14 u1)) (st2 c k s) ha3
  have hBeq : run k (st2 c k s) blkB = st3 c k s := rfl
  have ha4' : AgreeBelow cursor u4 (st3 c k s) := by rw [← hBeq]; exact ha4
  have hne4 : u4 22 ≠ 0 := by rw [ha4' 22 (by decide)]; exact h22
  have ha5 : AgreeBelow cursor (litDivStep 23 (2 ^ 44) 22 u4) (st4 c k s) :=
    litDivStep_congr 23 (2 ^ 44) 22 (by decide) ha4'
  -- stage C
  obtain ⟨u6, hu6, ha6⟩ := blockStep_agree k blkC blkC_wf
    (litDivStep 23 (2 ^ 44) 22 u4) (st4 c k s) ha5
  have hCeq : run k (st4 c k s) blkC = st5 c k s := rfl
  have ha6' : AgreeBelow cursor u6 (st5 c k s) := by rw [← hCeq]; exact ha6
  have hne6 : u6 44 ≠ 0 := by rw [ha6' 44 (by decide)]; exact h44
  have ha7 : AgreeBelow cursor (divStep 45 Op.udiv 43 44 u6) (st6 c k s) :=
    divStep_congr 45 Op.udiv 43 44 (by decide) (by decide) ha6'
  -- stage D
  obtain ⟨u8, hu8, ha8⟩ := blockStep_agree k blkD blkD_wf
    (divStep 45 Op.udiv 43 44 u6) (st6 c k s) ha7
  -- ⚠ the only one of the five that is NOT `rfl`: a bare `rfl` here diverges
  -- at `whnf`, while peeling the append first is instant.
  have hDeq : run k (st6 c k s) blkD = st7 c k s := by
    show run k (st6 c k s) (blkD1 ++ blkD2) = _
    rw [run_append]
    rfl
  have ha8' : AgreeBelow cursor u8 (st7 c k s) := by rw [← hDeq]; exact ha8
  have hne8 : u8 49 ≠ 0 := by rw [ha8' 49 (by decide)]; exact h49
  have ha9 : AgreeBelow cursor (divStep 50 Op.udiv 48 49 u8) (st8 c k s) :=
    divStep_congr 50 Op.udiv 48 49 (by decide) (by decide) ha8'
  -- stage F
  obtain ⟨u10, hu10, ha10⟩ := blockStep_agree k (blkF c) (blkF_wf c)
    (divStep 50 Op.udiv 48 49 u8) (st8 c k s) ha9
  have hFeq : run k (st8 c k s) (blkF c) = gRun c k s := rfl
  have ha10' : AgreeBelow cursor u10 (gRun c k s) := by
    rw [← hFeq]; exact ha10
  refine ⟨u10, ?_, ha10'⟩
  rw [hsplit, denoteInstrs_append, step1, obindSome,
    denoteInstrs_append, hu1, obindSome,
    denoteInstrs_append, udivStep_denote k 19 1 14 u1 hne1, obindSome,
    denoteInstrs_append,
    udivStep_denote k 20 19 14 (divStep 19 Op.udiv 1 14 u1) hne2, obindSome,
    denoteInstrs_append, hu4, obindSome,
    denoteInstrs_append, litDivStep_denote k 23 (2 ^ 44) 22 u4 hne4, obindSome,
    denoteInstrs_append, hu6, obindSome,
    denoteInstrs_append, udivStep_denote k 45 43 44 u6 hne6, obindSome,
    denoteInstrs_append, hu8, obindSome,
    denoteInstrs_append, udivStep_denote k 50 48 49 u8 hne8, obindSome,
    hu10]

/-! ## §11 The step function the fold bridge wants -/

/-- What the emitted body actually leaves in every register. -/
def gStep (c : Params) (k : Nat) (s : RegState) : RegState :=
  (denoteInstrs k s (gBody c)).getD s

/-- The machine step, at a visited index and under the invariant: defined,
its effect on the carried registers is `gRound`, and `Inv` is preserved. -/
theorem gStep_spec (hc : c.Sane) (hk : k < c.len * c.R) (hs : Inv c s) :
    denoteInstrs k s (gBody c) = some (gStep c k s) ∧
      valsOf (gStep c k s) = gRound c k (valsOf s) ∧
      Inv c (gStep c k s) := by
  obtain ⟨d14, d22, d44, d49⟩ := gRun_divs hc hk hs
  obtain ⟨u, hu, hag⟩ := gBody_defined hc d14 d22 d44 d49
  obtain ⟨hv, hI⟩ := gRun_spec hc hk hs
  have hstep : gStep c k s = u := by simp [gStep, hu]
  refine ⟨by rw [hstep]; exact hu, ?_, ?_⟩
  · rw [hstep, ← hv]
    show (⟨u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, u 9, u 10⟩ : Vals) = _
    rw [hag 0 (by decide), hag 1 (by decide), hag 2 (by decide),
      hag 3 (by decide), hag 4 (by decide), hag 5 (by decide),
      hag 6 (by decide), hag 7 (by decide), hag 8 (by decide),
      hag 9 (by decide), hag 10 (by decide)]
    rfl
  · rw [hstep]
    exact
      { word := TrialDivisionFold.denoteInstrs_lt k (gBody c) s u hu hs.word
        mPos := by rw [hag 1 (by decide)]; exact hI.mPos
        phiPos := by rw [hag 2 (by decide)]; exact hI.phiPos
        prod := by rw [hag 1 (by decide), hag 2 (by decide)]; exact hI.prod
        sqLe := by rw [hag 3 (by decide)]; exact hI.sqLe
        passLe := by rw [hag 6 (by decide)]; exact hI.passLe
        goodLe := by rw [hag 0 (by decide)]; exact hI.goodLe
        xULt := by rw [hag 7 (by decide)]; exact hI.xULt
        kULe := by rw [hag 8 (by decide)]; exact hI.kULe
        xLLt := by rw [hag 9 (by decide)]; exact hI.xLLt
        kLLe := by rw [hag 10 (by decide)]; exact hI.kLLe }

end Denote

/-! ## §12 Initialisation, the epilogue, and the whole program -/

/-- The carried registers after `gInit`: `gInit` moves `1` into registers
`0`, `1` and `2` and leaves every other register at the all-zero
`initialState`. -/
def initVals (c : Params) : Vals := ⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The register file after `gInit`. -/
def gInitState : RegState :=
  ((initialState.set 0 (1 % M)).set 1 (1 % M)).set 2 (1 % M)

theorem gInit_denote : denoteInstrs 0 initialState gInit = some gInitState := rfl

theorem gInitState_vals :
    gInitState 0 = 1 ∧ gInitState 1 = 1 ∧ gInitState 2 = 1 ∧
    gInitState 3 = 0 ∧ gInitState 4 = 0 ∧ gInitState 5 = 0 ∧
    gInitState 6 = 0 ∧ gInitState 7 = 0 ∧ gInitState 8 = 0 ∧
    gInitState 9 = 0 ∧ gInitState 10 = 0 := by
  have h1M : (1:Nat) % M = 1 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gInitState, RegState.set, initialState, h1M]

theorem valsOf_gInitState (c : Params) : valsOf gInitState = initVals c := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := gInitState_vals
  simp [valsOf, initVals, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

theorem gInitState_inv (c : Params) (hc : c.Sane) : Inv c gInitState := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := gInitState_vals
  have hlo := hc.loPos
  have hlen := hc.lenPos
  exact
    { word := by
        intro i
        simp only [gInitState, RegState.set, initialState]
        split
        · exact Nat.mod_lt _ M_pos
        · split
          · exact Nat.mod_lt _ M_pos
          · split
            · exact Nat.mod_lt _ M_pos
            · exact M_pos
      mPos := by rw [e1]; omega
      phiPos := by rw [e2]; omega
      prod := by rw [e1, e2]; omega
      sqLe := by rw [e3]; omega
      passLe := by rw [e6]; omega
      goodLe := by rw [e0]; omega
      xULt := by rw [e7]; simp only [MB]; omega
      kULe := by rw [e8]; simp only [KCAP]; omega
      xLLt := by rw [e9]; simp only [MB]; omega
      kLLe := by rw [e10]; simp only [KCAP]; omega }

/-- The epilogue's machine state: the compiled `blkEp` also writes the
expression compiler's temporaries, so this is `denoteInstrs`' own answer, not
`run`'s. -/
def gEpi (c : Params) (s : RegState) : RegState :=
  (denoteInstrs 0 s (block cursor (blkEp c))).getD s

theorem gEpi_denote (c : Params) (s : RegState) :
    denoteInstrs 0 s (block cursor (blkEp c)) = some (gEpi c s) := by
  obtain ⟨s', h1, _⟩ := block_correct 0 cursor (blkEp c) (blkEp_wf c) s
  rw [h1]
  simp [gEpi, h1]

theorem gEpi_zero (c : Params) (s : RegState) :
    gEpi c s 0 = run 0 s (blkEp c) 0 := by
  obtain ⟨s', h1, h2⟩ := block_correct 0 cursor (blkEp c) (blkEp_wf c) s
  have : gEpi c s = s' := by simp [gEpi, h1]
  rw [this]
  exact h2 0 (by decide)

/-- The good flag after the epilogue's two exact final-sum tests. -/
def gFinal (c : Params) (v : Vals) : Nat :=
  v.good * ((if v.accU ≤ c.finU then 1 else 0) * (if c.finL ≤ v.accL then 1 else 0))

/-- The epilogue, read off the carried registers. -/
theorem gEpi_val (c : Params) (hc : c.Sane) (s : RegState) (hs : Inv c s) :
    gEpi c s 0 = gFinal c (valsOf s) := by
  have hfinU : c.finU % M = c.finU :=
    modId (Nat.lt_trans hc.finLt.1 two56_lt_M)
  have hfinL : c.finL % M = c.finL :=
    modId (Nat.lt_trans hc.finLt.2 two56_lt_M)
  have hval : run 0 s (blkEp c) 0 =
      (s 0 * (((if s 4 ≤ c.finU % M then 1 else 0) *
        (if c.finL % M ≤ s 5 then 1 else 0)) % M)) % M := by
    show run 0 s [(⟨0, _⟩ : Assign)] 0 = _
    rw [run_cons, run_nil, set_at, evalMul, evalMul, evalLe, evalLe, evalReg,
      evalReg, evalReg, evalLit, evalLit]
  have hb1 : (if s 4 ≤ c.finU then (1:Nat) else 0) ≤ 1 := bitLe _
  have hb2 : (if c.finL ≤ s 5 then (1:Nat) else 0) ≤ 1 := bitLe _
  have hprod : ((if s 4 ≤ c.finU then (1:Nat) else 0) *
      (if c.finL ≤ s 5 then 1 else 0)) ≤ 1 := by
    have := Nat.mul_le_mul hb1 hb2
    omega
  have hprodM : ((if s 4 ≤ c.finU then (1:Nat) else 0) *
      (if c.finL ≤ s 5 then 1 else 0)) % M =
      (if s 4 ≤ c.finU then 1 else 0) * (if c.finL ≤ s 5 then 1 else 0) := by
    refine modId ?_
    have h2 : (2:Nat) ≤ M := by decide
    omega
  have hgood := hs.goodLe
  have houtM : (s 0 * ((if s 4 ≤ c.finU then (1:Nat) else 0) *
      (if c.finL ≤ s 5 then 1 else 0))) % M =
      s 0 * ((if s 4 ≤ c.finU then 1 else 0) * (if c.finL ≤ s 5 then 1 else 0)) := by
    refine modId ?_
    have := Nat.mul_le_mul hgood hprod
    have h2 : (2:Nat) ≤ M := by decide
    omega
  rw [gEpi_zero, hval, hfinU, hfinL, hprodM, houtM]
  rfl

/-- Every prefix of the loop carries the invariant, and reads off as the
corresponding prefix of the `gRound` fold. -/
theorem gFold_spec (c : Params) (hc : c.Sane) :
    ∀ N, N ≤ c.len * c.R → ∀ u, Inv c u →
      valsOf ((List.range N).foldl (fun w i => gStep c i w) u) =
          (List.range N).foldl (fun v i => gRound c i v) (valsOf u) ∧
        Inv c ((List.range N).foldl (fun w i => gStep c i w) u) := by
  intro N
  induction N with
  | zero => intro _ u hu; exact ⟨rfl, hu⟩
  | succ N ih =>
      intro hN u hu
      obtain ⟨ihv, ihI⟩ := ih (by omega) u hu
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
      obtain ⟨_, hv, hI⟩ := gStep_spec hc (k := N) (by omega) ihI
      exact ⟨by rw [hv, ihv], hI⟩

/-- **The program denotes the epilogue-corrected good flag of the flat
fold.** -/
theorem gProgram_denote (c : Params) (hc : c.Sane) :
    (gProgram c).denote =
      some (gFinal c ((List.range (c.len * c.R)).foldl
        (fun v k => gRound c k v) (initVals c))) := by
  have hI0 := gInitState_inv c hc
  have hden := RS62LadderEncoding.Program.denote_eq_foldl_mem (gProgram c)
    (Inv c) (gStep c) (gEpi c) gInitState gInit_denote hI0
    (fun index u hidx hu => (gStep_spec hc (k := index) hidx hu).1)
    (fun index u hidx hu => (gStep_spec hc (k := index) hidx hu).2.2)
    (fun u _ => gEpi_denote c u)
  obtain ⟨hFv, hFI⟩ :=
    gFold_spec c hc (c.len * c.R) (Nat.le_refl _) gInitState hI0
  rw [valsOf_gInitState c] at hFv
  rw [hden]
  show some (gEpi c ((List.range (c.len * c.R)).foldl
    (fun w i => gStep c i w) gInitState) 0) = _
  rw [gEpi_val c hc _ hFI, hFv]

/-- **Re-blocked**: the flat fold is the per-candidate fold of `R`-round
blocks. -/
theorem gFold_blocked (c : Params) :
    (List.range (c.len * c.R)).foldl (fun v k => gRound c k v) (initVals c) =
      (List.range c.len).foldl
        (BlockedFold.block c.R (fun v k => gRound c k v)) (initVals c) :=
  BlockedFold.foldl_range_mul c.len c.R (fun v k => gRound c k v) (initVals c)

end LeanCompCert.Ports.G1215Check

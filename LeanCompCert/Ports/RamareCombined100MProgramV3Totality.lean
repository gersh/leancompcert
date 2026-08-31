import LeanCompCert.Ports.RamareCombined100MProgramV3Denote
import LeanCompCert.Ports.RamareCombined100MLogCellsBounds
import LeanCompCert.Ports.RamareCombined100MShapeHostTotality

/-!
# Partial-semantics totality for the V3 combined program

This file keeps `AllDefined` proofs separate from the arithmetic refinement.
The proofs are symbolic in the configuration and never execute a sweep.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.PsiSegSieve (storeLit storeLits seedRegs)

/-- A literal array store is defined when its statically named cell is in the
allocated array and representable as a machine word. -/
theorem storeLit_defined (len k cell value : Nat) (s : AState)
    (hlen : cell < len) (hword : cell < M) :
    AllDefined len k s (storeLit cell value) := by
  simp [storeLit, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand,
    AState.writeReg, hlen, Nat.mod_eq_of_lt hword]

/-- A finite literal table is defined from pointwise address bounds. -/
theorem storeLits_defined (len k : Nat) (xs : List (Nat × Nat)) (s : AState)
    (hlen : ∀ x ∈ xs, x.1 < len) (hword : ∀ x ∈ xs, x.1 < M) :
    AllDefined len k s (storeLits xs) := by
  induction xs generalizing s with
  | nil => simp [storeLits, AllDefined]
  | cons x xs ih =>
      rw [storeLits, List.flatMap_cons, AllDefined_append]
      constructor
      · exact storeLit_defined len k x.1 x.2 s
          (hlen x (by simp)) (hword x (by simp))
      · apply ih
        · intro y hy
          exact hlen y (by simp [hy])
        · intro y hy
          exact hword y (by simp [hy])

/-- Register literal seeding contains no partial operation. -/
theorem seedRegs_defined (len k : Nat) (xs : List (Nat × Nat)) (s : AState) :
    AllDefined len k s (seedRegs xs) := by
  induction xs generalizing s with
  | nil => simp [seedRegs, AllDefined]
  | cons x xs ih =>
      simp only [seedRegs, List.map_cons, AllDefined, ADefined]
      exact ⟨trivial, ih _⟩

/-- Every table address in the shape initializer lies in the V3 allocation. -/
theorem ProgramV3.shapeTableCell_lt_arrayLen
    (c : LambdaPsiSweep.Cfg) (x : Nat × Nat)
    (hx : x ∈ c.shape.tableCells) : x.1 < c.arrayLen + 1 := by
  rcases List.mem_append.mp hx with htable | hsentinel
  · rcases List.mem_map.mp htable with ⟨row, hrow, rfl⟩
    have hidx : row.2 < c.shape.table.length := by
      simpa using (List.mem_zipIdx hrow).2.1
    unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
      LambdaPsiSweep.Cfg.logSink LambdaPsiSweep.Cfg.logHiBase
      LambdaPsiSweep.Cfg.logLoBase LambdaPsiSweep.Cfg.logLen
      ShapeSieve.Cfg.arrayLen ShapeSieve.Cfg.resultBase
      ShapeSieve.Cfg.tableBase ShapeSieve.Cfg.tableLen
    omega
  · simp only [List.mem_singleton] at hsentinel
    subst x
    unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
      LambdaPsiSweep.Cfg.logSink LambdaPsiSweep.Cfg.logHiBase
      LambdaPsiSweep.Cfg.logLoBase LambdaPsiSweep.Cfg.logLen
      ShapeSieve.Cfg.arrayLen ShapeSieve.Cfg.resultBase
      ShapeSieve.Cfg.tableBase ShapeSieve.Cfg.tableLen
    omega

/-- Every log-table address lies in the V3 allocation. -/
theorem ProgramV3.logCell_lt_arrayLen
    (c : LambdaPsiSweep.Cfg) (x : Nat × Nat) (hx : x ∈ c.logCells) :
    x.1 < c.arrayLen + 1 := by
  have hrange := LambdaPsiSweep.logCells_address_range c x hx
  unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
  omega

/-- The full V3 initializer is defined under the single natural layout
condition that its allocation size is a machine word. -/
theorem ProgramV3.init_defined (c : LambdaPsiSweep.Cfg)
    (sd : LambdaPsiSweep.Seed) (weighted : Nat) (lo hi : Int)
    (harray : c.arrayLen + 1 ≤ M) :
    AllDefined (c.arrayLen + 1) 0 initialAState
      (ProgramV3.init c sd weighted lo hi) := by
  have hshape (t : AState) :
      AllDefined (c.arrayLen + 1) 0 t c.shape.init := by
    rw [ShapeSieve.Cfg.init, AllDefined_append]
    constructor
    · apply storeLits_defined
      · exact ProgramV3.shapeTableCell_lt_arrayLen c
      · intro x hx
        exact Nat.lt_of_lt_of_le
          (ProgramV3.shapeTableCell_lt_arrayLen c x hx) harray
    · exact seedRegs_defined _ _ _ _
  have hlog (t : AState) :
      AllDefined (c.arrayLen + 1) 0 t
        (LogSweep.init c.shape sd.log) := by
    rw [LogSweep.init, AllDefined_append]
    exact ⟨hshape t, seedRegs_defined _ _ _ _⟩
  have hlambda (t : AState) :
      AllDefined (c.arrayLen + 1) 0 t
        (LambdaPsiSweep.init c sd) := by
    rw [LambdaPsiSweep.init, AllDefined_append]
    constructor
    · rw [AllDefined_append]
      constructor
      · exact hlog t
      · apply storeLits_defined
        · exact ProgramV3.logCell_lt_arrayLen c
        · intro x hx
          exact Nat.lt_of_lt_of_le
            (ProgramV3.logCell_lt_arrayLen c x hx) harray
    · exact seedRegs_defined _ _ _ _
  rw [ProgramV3.init, AllDefined_append]
  constructor
  · exact hlambda initialAState
  · simp [ProgramV3.initWide, movLit, AllDefined, ADefined]

/-- The partial initializer semantics agrees with its total `arun`. -/
theorem ProgramV3.init_denote (c : LambdaPsiSweep.Cfg)
    (sd : LambdaPsiSweep.Seed) (weighted : Nat) (lo hi : Int)
    (harray : c.arrayLen + 1 ≤ M) :
    denoteAInstrs (c.arrayLen + 1) 0 initialAState
        (ProgramV3.init c sd weighted lo hi) =
      some (arun 0 initialAState (ProgramV3.init c sd weighted lo hi)) :=
  denoteAInstrs_eq_arun _ _ _ _
    (ProgramV3.init_defined c sd weighted lo hi harray)

/-- The V3 epilogue stores only into the seven reserved result cells. -/
theorem ProgramV3.epilogue_defined (c : LambdaPsiSweep.Cfg) (s : AState)
    (harray : c.arrayLen + 1 ≤ M) :
    AllDefined (c.arrayLen + 1) 0 s (ProgramV3.epilogue c) := by
  have h5 : c.shape.resultBase + 5 < c.arrayLen + 1 := by
    unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
      LambdaPsiSweep.Cfg.logSink LambdaPsiSweep.Cfg.logHiBase
      LambdaPsiSweep.Cfg.logLoBase ShapeSieve.Cfg.arrayLen
      ShapeSieve.Cfg.resultBase
    omega
  have h0 : c.shape.resultBase < c.arrayLen + 1 := by omega
  have h1 : c.shape.resultBase + 1 < c.arrayLen + 1 := by omega
  have h2 : c.shape.resultBase + 2 < c.arrayLen + 1 := by omega
  have h3 : c.shape.resultBase + 3 < c.arrayLen + 1 := by omega
  have h4 : c.shape.resultBase + 4 < c.arrayLen + 1 := by omega
  have hr0 : c.resultBase < c.arrayLen + 1 := by
    unfold LambdaPsiSweep.Cfg.arrayLen
    omega
  have hr1 : c.resultBase + 1 < c.arrayLen + 1 := by
    unfold LambdaPsiSweep.Cfg.arrayLen
    omega
  have hr2 : c.resultBase + 2 < c.arrayLen + 1 := by
    unfold LambdaPsiSweep.Cfg.arrayLen
    omega
  have hr3 : c.resultBase + 3 < c.arrayLen + 1 := by
    unfold LambdaPsiSweep.Cfg.arrayLen
    omega
  have hr4 : c.resultBase + 4 < c.arrayLen + 1 := by
    unfold LambdaPsiSweep.Cfg.arrayLen
    omega
  have hr5 : c.resultBase + 5 < c.arrayLen + 1 := by
    unfold LambdaPsiSweep.Cfg.arrayLen
    omega
  have hr6 : c.resultBase + 6 < c.arrayLen + 1 := by
    unfold LambdaPsiSweep.Cfg.arrayLen
    omega
  simp [ProgramV3.epilogue, epilogueV2, LambdaPsiSweep.epilogue,
    LogSweep.epilogue, ShapeSieve.Cfg.epilogue, LambdaPsiSweep.storeResult,
    foldSweepGuard, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, h0, h1, h2, h3, h4, h5,
    hr0, hr1, hr2, hr3, hr4, hr5, hr6,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h0 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h1 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h2 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h3 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h4 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h5 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hr0 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hr1 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hr2 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hr3 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hr4 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hr5 harray),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hr6 harray)]

/-- The partial epilogue semantics agrees with its total `arun`. -/
theorem ProgramV3.epilogue_denote (c : LambdaPsiSweep.Cfg) (s : AState)
    (harray : c.arrayLen + 1 ≤ M) :
    denoteAInstrs (c.arrayLen + 1) 0 s (ProgramV3.epilogue c) =
      some (arun 0 s (ProgramV3.epilogue c)) :=
  denoteAInstrs_eq_arun _ _ _ _ (ProgramV3.epilogue_defined c s harray)

/-! ## Body staging

Only divisions and array accesses can be partial.  This small syntactic
predicate retires the V3 gate/carry stages without expanding their states. -/

def ANoPartial : AInstr → Bool
  | .scalar (.mov _ _) => true
  | .scalar (.binop _ op _ _) => op != .udiv && op != .urem
  | .load _ _ => false
  | .store _ _ => false

theorem allDefined_of_all_noPartial (len k : Nat) :
    ∀ (xs : List AInstr) (s : AState), xs.all ANoPartial = true →
      AllDefined len k s xs := by
  intro xs
  induction xs with
  | nil => intro s _; trivial
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      refine ⟨?_, ih _ h.2⟩
      cases i with
      | load d r => simp [ANoPartial] at h
      | store r v => simp [ANoPartial] at h
      | scalar instr =>
          cases instr with
          | mov d src => trivial
          | binop d op l r =>
              simp only [ANoPartial, Bool.and_eq_true, bne_iff_ne] at h
              show (denoteOp op (denoteOperand k s.regs l)
                (denoteOperand k s.regs r)).isSome = true
              cases op <;> simp_all [denoteOp]

theorem ProgramV3.gatePre_defined (len k : Nat) (s : AState) :
    AllDefined len k s ProgramV3.gatePre := by
  apply allDefined_of_all_noPartial
  rfl

theorem candidateGateStep_defined (len k : Nat) (s : AState) :
    AllDefined len k s candidateGateStep := by
  apply allDefined_of_all_noPartial
  rfl

theorem ProgramV3.hostArithmeticOverflowChecks_defined
    (len k : Nat) (s : AState) :
    AllDefined len k s ProgramV3.hostArithmeticOverflowChecks := by
  apply allDefined_of_all_noPartial
  rfl

theorem ProgramV3.gatePost_defined (len k : Nat) (s : AState) :
    AllDefined len k s ProgramV3.gatePost := by
  apply allDefined_of_all_noPartial
  rfl

/-- The body totality obligation factors exactly through the unchanged host
and the candidate checker.  Gate, carry-audit, and restore stages contain no
partial operations. -/
theorem ProgramV3.body_defined_of_host_and_checks
    (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      egammaLo egammaHi len k : Nat) (s : AState)
    (hhost : AllDefined len k (arun k s ProgramV3.gatePre)
      (LambdaPsiSweep.body c))
    (hchecks : AllDefined len k
      (arun k (arun k (arun k s ProgramV3.gatePre)
        (LambdaPsiSweep.body c)) candidateGateStep)
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo
        cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi)) :
    AllDefined len k s
      (ProgramV3.body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
        lower logLen loBase hiBase sink egammaLo egammaHi) := by
  let host := LambdaPsiSweep.body c
  let checks := ProgramV3.candidateChecks gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  have h12 : AllDefined len k s (ProgramV3.gatePre ++ host) :=
    (AllDefined_append len k _ _ s).mpr
      ⟨ProgramV3.gatePre_defined len k s, hhost⟩
  have h123 : AllDefined len k s
      ((ProgramV3.gatePre ++ host) ++ candidateGateStep) :=
    (AllDefined_append len k _ _ s).mpr ⟨h12, by
      simpa only [host, arun_append] using
        candidateGateStep_defined len k
          (arun k (arun k s ProgramV3.gatePre) host)⟩
  have h1234 : AllDefined len k s
      (((ProgramV3.gatePre ++ host) ++ candidateGateStep) ++ checks) :=
    (AllDefined_append len k _ _ s).mpr ⟨h123, by
      simpa only [host, checks, arun_append] using hchecks⟩
  have h12345 : AllDefined len k s
      ((((ProgramV3.gatePre ++ host) ++ candidateGateStep) ++ checks) ++
        ProgramV3.hostArithmeticOverflowChecks) :=
    (AllDefined_append len k _ _ s).mpr ⟨h1234, by
      exact ProgramV3.hostArithmeticOverflowChecks_defined len k _⟩
  have hfull : AllDefined len k s
      (((((ProgramV3.gatePre ++ host) ++ candidateGateStep) ++ checks) ++
        ProgramV3.hostArithmeticOverflowChecks) ++ ProgramV3.gatePost) :=
    (AllDefined_append len k _ _ s).mpr ⟨h12345,
      ProgramV3.gatePost_defined len k _⟩
  simpa only [ProgramV3.body, host, checks, List.append_assoc] using hfull

/-- Exact theorem-shaped remainder for one V3 body invocation. -/
def ProgramV3.BodyPartialGuards
    (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      egammaLo egammaHi len k : Nat) (s : AState) : Prop :=
  AllDefined len k (arun k s ProgramV3.gatePre) (LambdaPsiSweep.body c) ∧
    AllDefined len k
      (arun k (arun k (arun k s ProgramV3.gatePre)
        (LambdaPsiSweep.body c)) candidateGateStep)
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo
        cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi)

theorem ProgramV3.body_denote_of_partialGuards
    (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      egammaLo egammaHi len k : Nat) (s : AState)
    (h : ProgramV3.BodyPartialGuards c gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
      len k s) :
    denoteAInstrs len k s
        (ProgramV3.body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
          lower logLen loBase hiBase sink egammaLo egammaHi) =
      some (arun k s
        (ProgramV3.body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
          lower logLen loBase hiBase sink egammaLo egammaHi)) :=
  denoteAInstrs_eq_arun _ _ _ _
    (ProgramV3.body_defined_of_host_and_checks c gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi len k s h.1 h.2)

/-! ## Whole-program symbolic bridge -/

/-- Exact invariant-shaped residual for a complete V3 loop.  It contains
only the dynamic partial-operation guards for one body step and closure under
the total `arun`; neither this definition nor its consumer executes a loop. -/
def ProgramV3.LoopTotalityInvariant
    (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (P : AState → Prop) : Prop :=
  let p := ProgramV3.program c sd weighted lo hi gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  P (arun 0 initialAState p.init) ∧
    ∀ index s, index < p.loopCount → P s →
      ProgramV3.BodyPartialGuards c gammaLo gammaHi bound limit cgammaLo
        cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
        p.arrayLen index s ∧
      P (arun index s p.body)

/-- A proof of the exact loop-totality invariant turns the partial V3 program
denotation into the pure symbolic fold.  Initialization and epilogue
partiality are discharged once here, parametrically in the configuration. -/
theorem ProgramV3.program_denote_of_loopTotalityInvariant
    (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (P : AState → Prop) (harray : c.arrayLen + 1 ≤ M)
    (hP : ProgramV3.LoopTotalityInvariant c sd weighted lo hi gammaLo gammaHi
      bound limit cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      egammaLo egammaHi P) :
    let p := ProgramV3.program c sd weighted lo hi gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    p.denote =
      some ((arun 0
        ((List.range p.loopCount).foldl
          (fun s index => arun index s p.body)
          (arun 0 initialAState p.init)) p.epilogue).regs p.output) := by
  let p := ProgramV3.program c sd weighted lo hi gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
  dsimp only
  apply AProgram.denote_eq_foldl_mem p P
    (fun index s => arun index s p.body) (fun s => arun 0 s p.epilogue)
    (arun 0 initialAState p.init)
  · change denoteAInstrs (c.arrayLen + 1) 0 initialAState
        (ProgramV3.init c sd weighted lo hi) = _
    exact ProgramV3.init_denote c sd weighted lo hi harray
  · exact hP.1
  · intro index s hindex hs
    change denoteAInstrs (c.arrayLen + 1) index s
        (ProgramV3.body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
          lower logLen loBase hiBase sink egammaLo egammaHi) = _
    exact ProgramV3.body_denote_of_partialGuards c gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi (c.arrayLen + 1) index s (hP.2 index s hindex hs).1
  · intro index s hindex hs
    exact (hP.2 index s hindex hs).2
  · intro s _
    change denoteAInstrs (c.arrayLen + 1) 0 s (ProgramV3.epilogue c) = _
    exact ProgramV3.epilogue_denote c s harray

/-! ## Candidate-check divisor cut -/

def ProgramV3.candidateChecksAfterCurrent
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) : List AInstr :=
  seamPsiBlockAt ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR rTwoB ++
    ProgramV3.correctedRowCheckedAt ProgramV3.rPsiAtNLQ
      ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR cgammaLo cgammaHi cbound lower ++
    ProgramV3.anchorRowChecked gammaLo gammaHi bound limit ++
    pLogRecompute ++ qLogRecompute logLen loBase hiBase sink ++
    WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
    WideEndpoint.upperEndpoint logLen hiBase sink egammaHi ++
    weightedStep ++ ProgramV3.weightedOverflowCheck ++
    ProgramV3.literalAddCarryCheck rAccW 1 ++
    WideMagnitude.intervalMagnitudeWide ++ ProgramV3.rowWideChecks

theorem ProgramV3.candidateChecks_eq_current_cut
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi =
      candidateChecksV1 ++ ProgramV3.currentPsiAtNStage ++
        ProgramV3.candidateChecksAfterCurrent gammaLo gammaHi bound limit
          cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
          egammaLo egammaHi := by
  simp [ProgramV3.candidateChecks, ProgramV3.candidateChecksV2,
    ProgramV3.candidateChecksAfterCurrent, List.append_assoc]

set_option maxRecDepth 100000 in
/-- `currentPsiAtNStage` contributes no remaining partiality obligation: its
definedness follows from word closure of the prefix. -/
theorem ProgramV3.candidateChecks_defined_of_outer_stages
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi len k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (hbefore : AllDefined len k s candidateChecksV1)
    (hafter : AllDefined len k
      (arun k (arun k s candidateChecksV1) ProgramV3.currentPsiAtNStage)
      (ProgramV3.candidateChecksAfterCurrent gammaLo gammaHi bound limit
        cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
        egammaLo egammaHi)) :
    AllDefined len k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo
        cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi) := by
  have wpref := arun_word k candidateChecksV1 s hw ha
  have hprefix : AllDefined len k s
      (candidateChecksV1 ++ ProgramV3.currentPsiAtNStage) :=
    (AllDefined_append len k _ _ s).mpr
      ⟨hbefore, ProgramV3.currentPsiAtNStage_defined len k _ wpref.1⟩
  have hfull : AllDefined len k s
      ((candidateChecksV1 ++ ProgramV3.currentPsiAtNStage) ++
        ProgramV3.candidateChecksAfterCurrent gammaLo gammaHi bound limit
          cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
          egammaLo egammaHi) :=
    (AllDefined_append len k _ _ s).mpr ⟨hprefix, by
      simpa only [arun_append] using hafter⟩
  simpa only [ProgramV3.candidateChecks_eq_current_cut, List.append_assoc]
    using hfull

/-! ## Candidate outer stages

The candidate verifier has only three sources of partiality after the
normalized current-psi divisor: the table loads in `qLogRecompute`, the lower
endpoint, and the upper endpoint.  The remaining blocks are scalar and the
weighted divisor is normalized to one on marking rounds. -/

set_option maxRecDepth 100000 in
theorem candidateChecksV1_defined (len k : Nat) (s : AState) :
    AllDefined len k s candidateChecksV1 := by
  apply allDefined_of_all_noPartial
  rfl

theorem seamPsiBlockAt_defined (len k : Nat) (s : AState)
    (q r twoB : Nat) : AllDefined len k s (seamPsiBlockAt q r twoB) := by
  apply allDefined_of_all_noPartial
  rfl

set_option maxRecDepth 100000 in
theorem ProgramV3.correctedRowCheckedAt_defined (len k : Nat) (s : AState)
    (qL qU rU gammaLo gammaHi bound lower : Nat) :
    AllDefined len k s
      (ProgramV3.correctedRowCheckedAt qL qU rU gammaLo gammaHi bound lower) := by
  apply allDefined_of_all_noPartial
  rfl

set_option maxRecDepth 100000 in
theorem ProgramV3.anchorRowChecked_defined (len k : Nat) (s : AState)
    (gammaLo gammaHi bound limit : Nat) :
    AllDefined len k s
      (ProgramV3.anchorRowChecked gammaLo gammaHi bound limit) := by
  apply allDefined_of_all_noPartial
  rfl

set_option maxRecDepth 100000 in
theorem pLogRecompute_defined (len k : Nat) (s : AState) :
    AllDefined len k s pLogRecompute := by
  apply allDefined_of_all_noPartial
  rfl

/-- Proof-only cut immediately before the weighted quotient/remainder. -/
def weightedStepBeforeDiv : List AInstr :=
  absOf rWmag rIlo ++ absOf rWq rIhi ++
  [ .scalar (.binop rT4 .ge (.reg rWmag) (.reg rWq))
  , .scalar (.binop rT5 .lt (.reg rWmag) (.reg rWq))
  , .scalar (.binop rA .mul (.reg rT4) (.reg rWmag))
  , .scalar (.binop rB .mul (.reg rT5) (.reg rWq))
  , .scalar (.binop rWmag .add (.reg rA) (.reg rB))
  , .scalar (.binop rB .eq (.reg sCand) (.lit 0))
  , .scalar (.binop rB .add (.reg rB) (.reg sCand)) ]

def weightedStepFromDiv : List AInstr :=
  [ .scalar (.binop rA .udiv (.reg rWmag) (.reg rB))
  , .scalar (.binop rT4 .urem (.reg rWmag) (.reg rB))
  , .scalar (.binop rT5 .ne (.reg rT4) (.lit 0))
  , .scalar (.binop rA .add (.reg rA) (.reg rT5))
  , .scalar (.binop rAccW .add (.reg rAccW) (.reg rA)) ]

theorem weightedStep_eq_div_cut :
    weightedStep = weightedStepBeforeDiv ++ weightedStepFromDiv := by
  simp [weightedStep, weightedStepBeforeDiv, weightedStepFromDiv]

theorem weightedStepBeforeDiv_defined (len k : Nat) (s : AState) :
    AllDefined len k s weightedStepBeforeDiv := by
  apply allDefined_of_all_noPartial
  rfl

theorem weightedStepBeforeDiv_rB (k : Nat) (s : AState) :
    (arun k s weightedStepBeforeDiv).regs rB =
      ((if s.regs sCand = 0 then 1 else 0) + s.regs sCand) % M := by
  let mags := absOf rWmag rIlo ++ absOf rWq rIhi
  let sm := arun k s mags
  have hcand : sm.regs sCand = s.regs sCand := by
    dsimp only [sm, mags]
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k sCand _ (by rfl) s
  have hcand' : sm.regs 132 = s.regs 132 := by
    simpa only [sCand] using hcand
  rw [weightedStepBeforeDiv]
  change (arun k sm _).regs rB = _
  simp [arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rWmag, rWq, rT4, rT5, rA, rB, sCand, hcand']
  rfl

/-- The weighted update's divisor is `sCand + (sCand = 0)`, hence nonzero on
every word state, including marking rounds. -/
theorem weightedStep_defined (len k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) : AllDefined len k s weightedStep := by
  rw [weightedStep_eq_div_cut, AllDefined_append]
  refine ⟨weightedStepBeforeDiv_defined len k s, ?_⟩
  have hguard :
      ¬ (((if s.regs sCand = 0 then 1 else 0) + s.regs sCand) % M = 0) := by
    by_cases hz : s.regs sCand = 0
    · simp [hz, M]
    · simp [hz, Nat.mod_eq_of_lt (hw sCand)]
  have hb := weightedStepBeforeDiv_rB k s
  have hbn : (arun k s weightedStepBeforeDiv).regs rB ≠ 0 := by
    rw [hb]
    exact hguard
  have hbn' : (arun k s weightedStepBeforeDiv).regs 264 ≠ 0 := by
    simpa only [rB] using hbn
  simp [weightedStepFromDiv, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rA, rB, rT4, rT5, rWmag, rAccW, hbn']

theorem ProgramV3.weightedOverflowCheck_defined
    (len k : Nat) (s : AState) :
    AllDefined len k s ProgramV3.weightedOverflowCheck := by
  apply allDefined_of_all_noPartial
  rfl

theorem ProgramV3.literalAddCarryCheck_defined
    (len k : Nat) (s : AState) (saved addend : Nat) :
    AllDefined len k s (ProgramV3.literalAddCarryCheck saved addend) := by
  apply allDefined_of_all_noPartial
  rfl

theorem WideMagnitude.intervalMagnitudeWide_defined
    (len k : Nat) (s : AState) :
    AllDefined len k s WideMagnitude.intervalMagnitudeWide := by
  apply allDefined_of_all_noPartial
  rfl

set_option maxRecDepth 100000 in
theorem ProgramV3.rowWideChecks_defined (len k : Nat) (s : AState) :
    AllDefined len k s ProgramV3.rowWideChecks := by
  apply allDefined_of_all_noPartial
  rfl

/-- All scalar stages between the normalized current-psi block and the first
q-log table load. -/
def ProgramV3.candidateChecksBetweenCurrentAndQ
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower : Nat) :
    List AInstr :=
  seamPsiBlockAt ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR rTwoB ++
    ProgramV3.correctedRowCheckedAt ProgramV3.rPsiAtNLQ
      ProgramV3.rPsiAtNUQ ProgramV3.rPsiAtNUR cgammaLo cgammaHi cbound lower ++
    ProgramV3.anchorRowChecked gammaLo gammaHi bound limit ++ pLogRecompute

set_option maxRecDepth 100000 in
theorem ProgramV3.candidateChecksBetweenCurrentAndQ_defined
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower len k : Nat)
    (s : AState) :
    AllDefined len k s
      (ProgramV3.candidateChecksBetweenCurrentAndQ gammaLo gammaHi bound limit
        cgammaLo cgammaHi cbound lower) := by
  apply allDefined_of_all_noPartial
  rfl

def ProgramV3.candidateChecksBeforeQ
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower : Nat) :
    List AInstr :=
  candidateChecksV1 ++ ProgramV3.currentPsiAtNStage ++
    ProgramV3.candidateChecksBetweenCurrentAndQ gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower

set_option maxRecDepth 100000 in
/-- The scalar prefix before the q-log loads preserves the classified `q`
register.  Caching the destination scan here keeps production specializations
from unfolding the full candidate instruction list. -/
theorem ProgramV3.candidateChecksBeforeQ_shapeQ_frame
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower k : Nat)
    (s : AState) :
    (arun k s (ProgramV3.candidateChecksBeforeQ gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower)).regs sShapeQ = s.regs sShapeQ := by
  exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k sShapeQ _ (by rfl) s

theorem ProgramV3.candidateChecksBeforeQ_defined
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower len k : Nat)
    (s : AState) (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    AllDefined len k s
      (ProgramV3.candidateChecksBeforeQ gammaLo gammaHi bound limit cgammaLo
        cgammaHi cbound lower) := by
  have wpref := arun_word k candidateChecksV1 s hw ha
  have hprefix : AllDefined len k s
      (candidateChecksV1 ++ ProgramV3.currentPsiAtNStage) :=
    (AllDefined_append len k _ _ s).mpr
      ⟨candidateChecksV1_defined len k s,
        ProgramV3.currentPsiAtNStage_defined len k _ wpref.1⟩
  rw [ProgramV3.candidateChecksBeforeQ, AllDefined_append]
  refine ⟨hprefix, ?_⟩
  simpa only [arun_append] using
    ProgramV3.candidateChecksBetweenCurrentAndQ_defined gammaLo gammaHi bound
      limit cgammaLo cgammaHi cbound lower len k _

/-- Scalar tail after both endpoint table-load stages.  The only partial
operations in this tail are the normalized weighted quotient/remainder, whose
definedness follows from word closure. -/
def ProgramV3.candidateChecksAfterUpper : List AInstr :=
  weightedStep ++ ProgramV3.weightedOverflowCheck ++
    ProgramV3.literalAddCarryCheck rAccW 1 ++
    WideMagnitude.intervalMagnitudeWide ++ ProgramV3.rowWideChecks

theorem ProgramV3.candidateChecksAfterUpper_defined
    (len k : Nat) (s : AState) (hw : ∀ j, s.regs j < M) :
    AllDefined len k s ProgramV3.candidateChecksAfterUpper := by
  rw [ProgramV3.candidateChecksAfterUpper]
  repeat' rw [AllDefined_append]
  refine ⟨⟨⟨⟨weightedStep_defined len k s hw,
    ProgramV3.weightedOverflowCheck_defined len k _⟩,
    ProgramV3.literalAddCarryCheck_defined len k _ rAccW 1⟩,
    WideMagnitude.intervalMagnitudeWide_defined len k _⟩,
    ProgramV3.rowWideChecks_defined len k _⟩

theorem ProgramV3.candidateChecks_eq_load_cut
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi =
      ProgramV3.candidateChecksBeforeQ gammaLo gammaHi bound limit cgammaLo
          cgammaHi cbound lower ++
        qLogRecompute logLen loBase hiBase sink ++
        WideEndpoint.lowerEndpoint logLen loBase sink egammaLo ++
        WideEndpoint.upperEndpoint logLen hiBase sink egammaHi ++
        ProgramV3.candidateChecksAfterUpper := by
  simp [ProgramV3.candidateChecks, ProgramV3.candidateChecksV2,
    ProgramV3.candidateChecksBeforeQ,
    ProgramV3.candidateChecksBetweenCurrentAndQ,
    ProgramV3.candidateChecksAfterUpper, List.append_assoc]

/-- A scalar q-index computation contains no partial operation. -/
theorem qIndexBlock_defined (logLen base sink len k : Nat) (s : AState) :
    AllDefined len k s (qIndexBlock logLen base sink) := by
  apply allDefined_of_all_noPartial
  rfl

theorem loadCell_defined (dst idx len k : Nat) (s : AState)
    (hidx : s.regs idx < len) :
    AllDefined len k s (loadCell dst idx) := by
  simp [loadCell, AllDefined, ADefined, hidx]

theorem shrReg_defined (dst src amount len k : Nat) (s : AState) :
    AllDefined len k s (shrReg dst src amount) := by
  apply allDefined_of_all_noPartial
  rfl

theorem ceilShift16Reg_defined (dst src len k : Nat) (s : AState) :
    AllDefined len k s (ceilShift16Reg dst src) := by
  apply allDefined_of_all_noPartial
  rfl

/-- Exact two-address residual for `qLogRecompute`. -/
def QLogLoadGuards (logLen loBase hiBase sink len k : Nat)
    (s : AState) : Prop :=
  let loIndex := arun k s (qIndexBlock logLen loBase sink)
  let loLoaded := arun k loIndex (loadCell rQLo rA)
  let loShifted := arun k loLoaded (shrReg rQLo rQLo 16)
  let hiIndex := arun k loShifted (qIndexBlock logLen hiBase sink)
  loIndex.regs rA < len ∧ hiIndex.regs rA < len

/-- Source-readable form of the two q-log address guards, plus the word
headroom needed to identify the branch-free index computations. -/
def QLogAddressGuards (logLen loBase hiBase sink len : Nat)
    (s : AState) : Prop :=
  logLen < M ∧ sink < M ∧
    s.regs sShapeQ + loBase < M ∧ s.regs sShapeQ + hiBase < M ∧
    (if s.regs sShapeQ < logLen then s.regs sShapeQ + loBase else sink) < len ∧
    (if s.regs sShapeQ < logLen then s.regs sShapeQ + hiBase else sink) < len

/-- The reserved fallback cell is inside the V3 allocation for every
lambda/psi configuration. -/
theorem qLogSink_lt_v3ArrayLen (c : LambdaPsiSweep.Cfg) :
    c.logSink < c.arrayLen + 1 := by
  unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
  omega

/-- A lower-table q index below `logLen` is inside the V3 allocation. -/
theorem qLogLoIndex_lt_v3ArrayLen
    (c : LambdaPsiSweep.Cfg) (q : Nat) (hq : q < c.logLen) :
    q + c.logLoBase < c.arrayLen + 1 := by
  unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
    LambdaPsiSweep.Cfg.logSink LambdaPsiSweep.Cfg.logHiBase
  omega

/-- An upper-table q index below `logLen` is inside the V3 allocation. -/
theorem qLogHiIndex_lt_v3ArrayLen
    (c : LambdaPsiSweep.Cfg) (q : Nat) (hq : q < c.logLen) :
    q + c.logHiBase < c.arrayLen + 1 := by
  unfold LambdaPsiSweep.Cfg.arrayLen LambdaPsiSweep.Cfg.resultBase
    LambdaPsiSweep.Cfg.logSink
  omega

/-- Constructor for the readable q-log guard from its six elementary
bounds. -/
theorem QLogAddressGuards.of_bounds
    (logLen loBase hiBase sink len : Nat) (s : AState)
    (hlogM : logLen < M) (hsinkM : sink < M)
    (hloM : s.regs sShapeQ + loBase < M)
    (hhiM : s.regs sShapeQ + hiBase < M)
    (hloLen : (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + loBase else sink) < len)
    (hhiLen : (if s.regs sShapeQ < logLen then
        s.regs sShapeQ + hiBase else sink) < len) :
    QLogAddressGuards logLen loBase hiBase sink len s :=
  ⟨hlogM, hsinkM, hloM, hhiM, hloLen, hhiLen⟩

theorem QLogLoadGuards.of_addressGuards
    (logLen loBase hiBase sink len k : Nat) (s : AState)
    (h : QLogAddressGuards logLen loBase hiBase sink len s) :
    QLogLoadGuards logLen loBase hiBase sink len k s := by
  let loIndex := arun k s (qIndexBlock logLen loBase sink)
  let loLoaded := arun k loIndex (loadCell rQLo rA)
  let loShifted := arun k loLoaded (shrReg rQLo rQLo 16)
  let hiIndex := arun k loShifted (qIndexBlock logLen hiBase sink)
  have hlo := qIndexBlock_run k s logLen loBase sink h.1 h.2.1 h.2.2.1
  have hq0 : loIndex.regs sShapeQ = s.regs sShapeQ :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sShapeQ _ (by rfl) s
  have hq1 : loLoaded.regs sShapeQ = loIndex.regs sShapeQ :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sShapeQ _ (by rfl) loIndex
  have hq2 : loShifted.regs sShapeQ = loLoaded.regs sShapeQ :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k sShapeQ _ (by rfl) loLoaded
  have hq : loShifted.regs sShapeQ = s.regs sShapeQ := by
    rw [hq2, hq1, hq0]
  have hhi := qIndexBlock_run k loShifted logLen hiBase sink h.1 h.2.1
    (by rw [hq]; exact h.2.2.2.1)
  constructor
  · rw [hlo]
    exact h.2.2.2.2.1
  · rw [hhi, hq]
    exact h.2.2.2.2.2

theorem qLogDirectLoad_defined_of_guards
    (logLen loBase hiBase sink len k : Nat) (s : AState)
    (h : QLogLoadGuards logLen loBase hiBase sink len k s) :
    AllDefined len k s (qLogDirectLoad logLen loBase hiBase sink) := by
  let loIndex := arun k s (qIndexBlock logLen loBase sink)
  let loLoaded := arun k loIndex (loadCell rQLo rA)
  let loShifted := arun k loLoaded (shrReg rQLo rQLo 16)
  let hiIndex := arun k loShifted (qIndexBlock logLen hiBase sink)
  rw [qLogDirectLoad]
  repeat' rw [AllDefined_append]
  simpa only [arun_append] using
    ⟨⟨⟨⟨⟨qIndexBlock_defined logLen loBase sink len k s,
      loadCell_defined rQLo rA len k loIndex h.1⟩,
      shrReg_defined rQLo rQLo 16 len k loLoaded⟩,
      qIndexBlock_defined logLen hiBase sink len k loShifted⟩,
      loadCell_defined rQHi rA len k hiIndex h.2⟩,
      ceilShift16Reg_defined rQHi rQHi len k _⟩

set_option maxRecDepth 100000 in
theorem qLogRecomputeTail_defined (len k : Nat) (s : AState) :
    AllDefined len k s (qLogDerivedLower ++ qLogDerivedUpper ++ qLogSelect) := by
  apply allDefined_of_all_noPartial
  rfl

theorem qLogRecompute_defined_of_guards
    (logLen loBase hiBase sink len k : Nat) (s : AState)
    (h : QLogLoadGuards logLen loBase hiBase sink len k s) :
    AllDefined len k s (qLogRecompute logLen loBase hiBase sink) := by
  have hcut : qLogRecompute logLen loBase hiBase sink =
      qLogDirectLoad logLen loBase hiBase sink ++
        (qLogDerivedLower ++ qLogDerivedUpper ++ qLogSelect) := by
    simp [qLogRecompute, List.append_assoc]
  rw [hcut, AllDefined_append]
  exact ⟨qLogDirectLoad_defined_of_guards logLen loBase hiBase sink len k s h,
    qLogRecomputeTail_defined len k _⟩

set_option maxRecDepth 100000 in
theorem WideEndpoint.lowerEndpoint_defined
    (logLen loBase sink gammaLo len k : Nat) (s : AState) :
    AllDefined len k s
      (WideEndpoint.lowerEndpoint logLen loBase sink gammaLo) := by
  apply allDefined_of_all_noPartial
  rfl

set_option maxRecDepth 100000 in
theorem WideEndpoint.upperEndpoint_defined
    (logLen hiBase sink gammaHi len k : Nat) (s : AState) :
    AllDefined len k s
      (WideEndpoint.upperEndpoint logLen hiBase sink gammaHi) := by
  apply allDefined_of_all_noPartial
  rfl

/-- Strictly smaller exact candidate residual: only the two q-log table
addresses remain.  Both wide endpoint blocks consume the already-loaded q-log
registers and contain no partial instruction. -/
def ProgramV3.CandidateLoadGuards
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink len k : Nat)
    (s : AState) : Prop :=
  let before := ProgramV3.candidateChecksBeforeQ gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower
  let qState := arun k s before
  QLogAddressGuards logLen loBase hiBase sink len qState

/-- Package address guards at the exact state reached by the scalar prefix
without making downstream specializations unfold that prefix. -/
theorem ProgramV3.CandidateLoadGuards.of_qState
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink len k : Nat) (s : AState)
    (h : QLogAddressGuards logLen loBase hiBase sink len
      (arun k s (ProgramV3.candidateChecksBeforeQ gammaLo gammaHi bound limit
        cgammaLo cgammaHi cbound lower))) :
    ProgramV3.CandidateLoadGuards gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink len k s := h

theorem ProgramV3.candidateChecks_defined_of_loadGuards
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi len k : Nat)
    (s : AState) (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (hloads : ProgramV3.CandidateLoadGuards gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink len k s) :
    AllDefined len k s
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo
        cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi) := by
  let before := ProgramV3.candidateChecksBeforeQ gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower
  let qBlock := qLogRecompute logLen loBase hiBase sink
  let lowerBlock := WideEndpoint.lowerEndpoint logLen loBase sink egammaLo
  let upperBlock := WideEndpoint.upperEndpoint logLen hiBase sink egammaHi
  have hbefore : AllDefined len k s before := by
    exact ProgramV3.candidateChecksBeforeQ_defined gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower len k s hw ha
  have hq : AllDefined len k (arun k s before) qBlock :=
    qLogRecompute_defined_of_guards logLen loBase hiBase sink len k _
      (QLogLoadGuards.of_addressGuards logLen loBase hiBase sink len k _ hloads)
  have hlower : AllDefined len k (arun k (arun k s before) qBlock)
      lowerBlock := WideEndpoint.lowerEndpoint_defined logLen loBase sink
        egammaLo len k _
  have hupper : AllDefined len k
      (arun k (arun k (arun k s before) qBlock) lowerBlock)
      upperBlock := WideEndpoint.upperEndpoint_defined logLen hiBase sink
        egammaHi len k _
  have hthrough : AllDefined len k s
      (((before ++ qBlock) ++ lowerBlock) ++ upperBlock) := by
    repeat' rw [AllDefined_append]
    simpa only [arun_append] using ⟨⟨⟨hbefore, hq⟩, hlower⟩, hupper⟩
  have wpref := arun_word k
    (((before ++ qBlock) ++ lowerBlock) ++ upperBlock) s hw ha
  have hfull : AllDefined len k s
      ((((before ++ qBlock) ++ lowerBlock) ++ upperBlock) ++
        ProgramV3.candidateChecksAfterUpper) :=
    (AllDefined_append len k _ _ s).mpr ⟨hthrough, by
      exact ProgramV3.candidateChecksAfterUpper_defined len k _ wpref.1⟩
  simpa only [ProgramV3.candidateChecks_eq_load_cut, before, qBlock,
    lowerBlock, upperBlock, List.append_assoc] using hfull

/-- Reduced one-step residual: the unchanged host remains explicit, while the
candidate verifier has been reduced from its entire instruction list to two
dynamic q-log table addresses. -/
def ProgramV3.BodyDynamicGuards
    (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      _egammaLo _egammaHi len k : Nat) (s : AState) : Prop :=
  let gated := arun k s ProgramV3.gatePre
  let hosted := arun k gated (LambdaPsiSweep.body c)
  let candidate := arun k hosted candidateGateStep
  len = c.arrayLen + 1 ∧
    LambdaPsiSweep.ShapeHostInvariant c k gated ∧
    ProgramV3.CandidateLoadGuards gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink len k candidate

theorem ProgramV3.body_denote_of_dynamicGuards
    (c : LambdaPsiSweep.Cfg) (gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink
      egammaLo egammaHi len k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (h : ProgramV3.BodyDynamicGuards c gammaLo gammaHi bound limit cgammaLo
      cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
      len k s) :
    denoteAInstrs len k s
        (ProgramV3.body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
          lower logLen loBase hiBase sink egammaLo egammaHi) =
      some (arun k s
        (ProgramV3.body c gammaLo gammaHi bound limit cgammaLo cgammaHi cbound
          lower logLen loBase hiBase sink egammaLo egammaHi)) := by
  let candidate := arun k
    (arun k (arun k s ProgramV3.gatePre) (LambdaPsiSweep.body c))
    candidateGateStep
  have wgate := arun_word k ProgramV3.gatePre s hw ha
  have whost := arun_word k (LambdaPsiSweep.body c)
    (arun k s ProgramV3.gatePre) wgate.1 wgate.2
  have wcandidate := arun_word k candidateGateStep
    (arun k (arun k s ProgramV3.gatePre) (LambdaPsiSweep.body c))
    whost.1 whost.2
  have hhostActual : AllDefined (c.arrayLen + 1) k
      (arun k s ProgramV3.gatePre) (LambdaPsiSweep.body c) :=
    LambdaPsiSweep.body_defined_of_shapeHostInvariant c k _
      wgate.1 wgate.2 h.2.1
  have hhost : AllDefined len k (arun k s ProgramV3.gatePre)
      (LambdaPsiSweep.body c) := by
    rw [h.1]
    exact hhostActual
  have hchecks : AllDefined len k candidate
      (ProgramV3.candidateChecks gammaLo gammaHi bound limit cgammaLo cgammaHi
        cbound lower logLen loBase hiBase sink egammaLo egammaHi) :=
    ProgramV3.candidateChecks_defined_of_loadGuards gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi len k candidate wcandidate.1 wcandidate.2 h.2.2
  exact ProgramV3.body_denote_of_partialGuards c gammaLo gammaHi bound limit
    cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo egammaHi
    len k s ⟨hhost, hchecks⟩

/-! ## Shape-sieve dynamic stages -/

/-- The seven marking loads have exactly their seven address obligations. -/
theorem ShapeSieve.Cfg.markLoadBody_defined (len k : Nat) (s : AState)
    (h30 : s.regs 30 < len) (h31 : s.regs 31 < len)
    (h32 : s.regs 32 < len) (h33 : s.regs 33 < len)
    (h34 : s.regs 34 < len) (h35 : s.regs 35 < len)
    (h36 : s.regs 36 < len) :
    AllDefined len k s ShapeSieve.Cfg.markLoadBody := by
  simp [ShapeSieve.Cfg.markLoadBody, AllDefined, ADefined, astep,
    AState.writeReg, h30, h31, h32, h33, h34, h35, h36]

/-- The seven marking stores reuse the address registers and introduce no
additional arithmetic partiality. -/
theorem ShapeSieve.Cfg.markCellBody_defined (len k : Nat) (s : AState)
    (h30 : s.regs 30 < len) (h31 : s.regs 31 < len)
    (h32 : s.regs 32 < len) (h33 : s.regs 33 < len)
    (h34 : s.regs 34 < len) (h35 : s.regs 35 < len)
    (h36 : s.regs 36 < len) :
    AllDefined len k s ShapeSieve.Cfg.markCellBody := by
  simp [ShapeSieve.Cfg.markCellBody, ShapeSieve.Cfg.markAllProductBody,
    ShapeSieve.Cfg.markFirstBody, ShapeSieve.Cfg.markFirstSelectBody,
    ShapeSieve.Cfg.markFirstExponentBody, ShapeSieve.Cfg.markFirstProductBody,
    ShapeSieve.Cfg.markSecondBody, ShapeSieve.Cfg.markSecondSelectBody,
    ShapeSieve.Cfg.markSecondFlagsBody, ShapeSieve.Cfg.markSecondCommitBody,
    ShapeSieve.Cfg.markSecondExponentBody,
    ShapeSieve.Cfg.markSecondProductBody, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, AState.writeArr,
    h30, h31, h32, h33, h34, h35, h36]

/-- Reset's only partial operations are its two remainders by the first table
entry. -/
theorem ShapeSieve.Cfg.markResetBody_defined (c : ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hp : c.table.head?.getD 1 ≠ 0) (hpM : c.table.head?.getD 1 < M) :
    AllDefined len k s c.markResetBody := by
  simp [ShapeSieve.Cfg.markResetBody, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hp, Nat.mod_eq_of_lt hpM]

/-- Cursor offset advancement is defined exactly when its carried prime power
is nonzero. -/
theorem ShapeSieve.Cfg.markAdvanceOffsetBody_defined (c : ShapeSieve.Cfg)
    (len k : Nat) (s : AState) (hpow : s.regs ShapeSieve.rPow ≠ 0) :
    AllDefined len k s c.markAdvanceOffsetBody := by
  have hpow' : s.regs 3 ≠ 0 := by
    simpa only [ShapeSieve.rPow] using hpow
  simp [ShapeSieve.Cfg.markAdvanceOffsetBody, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, ShapeSieve.rPow, hpow']

end LeanCompCert.Ports.RamareCombined100M.SeamBlock

import LeanCompCert.Ports.R2SegSieve

/-!
# Dense compiled head for the `R₂*` sweep

The production segmented program normally streams only nonzero jump points.
That sparse schedule is efficient high in the range, but its deliberately
strong interval check is too coarse near `3`.  This variant appends every
non-jump integer to the stream with the existing zero-product payload
`mode = 1, first = 0, aux = 0`.  The unchanged compiled log body then computes
its logarithm, applies a zero jump, and checks both clauses at that integer.

Thus the head carry and the dense head inequalities are computed by compiled
code; Lean only verifies this literal program and its semantics.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

/-- Append the integers rejected by the ordinary four-way classifier.  A
qualifying integer was already appended by `classBody`, so exactly one stream
entry is produced for every accumulation cell. -/
def R2Cfg.denseClassSuffix (c : R2Cfg) : List AInstr :=
  [ .scalar (.binop 140 .sub (.lit 1) (.reg 115))
  , .scalar (.binop 141 .mul (.reg 140) (.reg 9))
  , .scalar (.binop 142 .lt (.reg rWc) (.lit c.streamCap))
  , .scalar (.binop 143 .mul (.reg 141) (.reg 142))
  , .scalar (.binop 144 .sub (.reg 141) (.reg 143))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 144))
  , .scalar (.binop rVCap .add (.reg rVCap) (.reg 144))
  , .scalar (.binop 145 .shl (.reg rWc) (.lit 1))
  , .scalar (.binop 146 .add (.reg 145) (.lit c.streamBase))
  , .scalar (.binop 147 .mul (.reg 143) (.reg 146))
  , .scalar (.binop 148 .sub (.lit 1) (.reg 143))
  , .scalar (.binop 149 .mul (.reg 148) (.lit c.streamSink))
  , .scalar (.binop 139 .add (.reg 147) (.reg 149))
  , .store 139 87
  , .scalar (.mov 140 (.lit (1 <<< 57)))
  , .scalar (.binop 139 .add (.reg 139) (.lit 1))
  , .store 139 140
  , .scalar (.binop rWc .add (.reg rWc) (.reg 143)) ]

/-- A synthetic dense entry is exactly `(mode = 1, first = 0)`.  The ordinary
event path has already added its (zero-jump) enclosure and term count; remove
those two artificial commits before clause two while retaining the finish bit
and `rPrev` advance used for the dense inequality check. -/
def denseLogCorrectionBody : List AInstr :=
  [ .scalar (.binop 360 .eq (.reg 242) (.lit 1))
  , .scalar (.binop 361 .eq (.reg 263) (.lit 0))
  , .scalar (.binop 362 .mul (.reg 360) (.reg 361))
  , .scalar (.binop 363 .mul (.reg 362) (.reg 247))
  , .scalar (.binop 364 .mul (.reg 363) (.reg 320))
  , .scalar (.binop rErr .sub (.reg rErr) (.reg 364))
  , .scalar (.binop rTerms .sub (.reg rTerms) (.reg 363)) ]

/-- Dense verification recomputes the logarithm even for production modes
2/3, whose jump factors do not otherwise need it. -/
def R2Cfg.denseScheduledLogBody (c : R2Cfg) : List AInstr :=
  c.logBody.take 53 ++ [.scalar (.mov 243 (.lit 0))] ++ c.logBody.drop 54

/-- The factor selector later reuses register 243.  Restore its production
meaning after scheduling has finished and before payload decoding. -/
def R2Cfg.denseAllLogBody (c : R2Cfg) : List AInstr :=
  c.denseScheduledLogBody.take 74 ++
    [.scalar (.binop 243 .ge (.reg 242) (.lit 2))] ++
    c.denseScheduledLogBody.drop 74

/-- With consecutive dense test points, clause one is evaluated at `n-1`.
The production sparse body deliberately charges `n` as a one-ulp-safe
shortcut; the dense head uses the exact integer required by the source fold. -/
def R2Cfg.denseClauseLogBody (c : R2Cfg) : List AInstr :=
  c.denseAllLogBody.take 109 ++
    [ .scalar (.binop 365 .sub (.reg rNe) (.lit 1))
    , .scalar (.binop 294 .add (.reg 293) (.reg 365)) ] ++
    c.denseAllLogBody.drop 110

/-- Production refreshes the majorant logarithm only when its jump factors
needed a logarithm.  Dense verification refreshes it at every finished entry. -/
def R2Cfg.denseRefreshLogBody (c : R2Cfg) : List AInstr :=
  c.denseClauseLogBody.take 129 ++
    [.scalar (.binop 306 .mul (.lit 1) (.reg 247))] ++
    c.denseClauseLogBody.drop 130

/-- The literature range begins at `3`; the first dense clause-one check
would otherwise inspect the seeded point `2`. -/
def R2Cfg.denseHeadClauseGateBody (c : R2Cfg) : List AInstr :=
  c.denseRefreshLogBody.take 113 ++
    [ .scalar (.binop 366 .gt (.reg rNe) (.lit 3))
    , .scalar (.binop 367 .mul (.reg 296) (.reg 366))
    , .scalar (.binop 297 .mul (.reg 367) (.reg 247)) ] ++
    c.denseRefreshLogBody.drop 114

def R2Cfg.denseLogBody (c : R2Cfg) : List AInstr :=
  c.denseHeadClauseGateBody.take 152 ++ denseLogCorrectionBody ++
    c.denseHeadClauseGateBody.drop 152

def R2Cfg.denseHeadBody (c : R2Cfg) : List AInstr :=
  c.markBody ++ (c.classBody ++ c.denseClassSuffix) ++
    c.denseLogBody ++ c.tailBody

/-- One-window dense-head configuration.  Every integer needs `sc` fixed-log
rounds in the worst case and one stream entry. -/
def R2Cfg.withDenseHeadBudgets (c : R2Cfg) : R2Cfg :=
  { c with
    logSteps := c.sc * c.segLen + 128
    streamCap := c.segLen + 128 }

/-- On a small prefix, name every prime rather than only primes through the
square root.  This selects the exact prime/prime-power convention used by the
source head fold while retaining a compact initializer when `hi` is small. -/
def R2Cfg.withFullFactorTable (c : R2Cfg) : R2Cfg :=
  { c with
    markSteps := markBudget c.hi c.hi c.segLen
    table := (primesBelow (c.hi + 1)).map
      (fun p => packEntry p (LeanCompCert.Ports.PsiSegSieve.lnFix c.sc p) 1) }

def r2DenseHeadProgram (c : R2Cfg) (s : R2Seed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.period * c.segCount
  init := c.init s
  body := c.denseHeadBody
  epilogue := c.epilogue
  output := outputReg
}

theorem denseClassSuffix_all (c : R2Cfg) :
    c.denseClassSuffix.all (ainstrWFB regCount) = true := by rfl

private theorem all_take_of_all {p : AInstr → Bool} {l : List AInstr}
    (h : l.all p = true) (n : Nat) : (l.take n).all p = true :=
  List.all_eq_true.mpr (fun x hx =>
    List.all_eq_true.mp h x (List.mem_of_mem_take hx))

private theorem all_drop_of_all {p : AInstr → Bool} {l : List AInstr}
    (h : l.all p = true) (n : Nat) : (l.drop n).all p = true :=
  List.all_eq_true.mpr (fun x hx =>
    List.all_eq_true.mp h x (List.mem_of_mem_drop hx))

private theorem all_splice_of_all {r : Nat} {l mid : List AInstr}
    (h : l.all (ainstrWFB r) = true)
    (hmid : mid.all (ainstrWFB r) = true) (a b : Nat) :
    (l.take a ++ mid ++ l.drop b).all (ainstrWFB r) = true :=
  all_append (all_append (all_take_of_all h a) hmid)
    (all_drop_of_all h b)

private theorem logBody_all (c : R2Cfg) :
    c.logBody.all (ainstrWFB regCount) = true := by rfl

theorem denseScheduledLogBody_all (c : R2Cfg) :
    c.denseScheduledLogBody.all (ainstrWFB regCount) = true := by
  apply all_splice_of_all (logBody_all c)
  rfl

theorem denseAllLogBody_all (c : R2Cfg) :
    c.denseAllLogBody.all (ainstrWFB regCount) = true := by
  apply all_splice_of_all (denseScheduledLogBody_all c)
  rfl

theorem denseClauseLogBody_all (c : R2Cfg) :
    c.denseClauseLogBody.all (ainstrWFB regCount) = true := by
  apply all_splice_of_all (denseAllLogBody_all c)
  rfl

theorem denseRefreshLogBody_all (c : R2Cfg) :
    c.denseRefreshLogBody.all (ainstrWFB regCount) = true := by
  apply all_splice_of_all (denseClauseLogBody_all c)
  rfl

theorem denseHeadClauseGateBody_all (c : R2Cfg) :
    c.denseHeadClauseGateBody.all (ainstrWFB regCount) = true := by
  apply all_splice_of_all (denseRefreshLogBody_all c)
  rfl

theorem denseLogBody_all (c : R2Cfg) :
    c.denseLogBody.all (ainstrWFB regCount) = true := by
  apply all_splice_of_all (denseHeadClauseGateBody_all c)
  rfl

set_option maxRecDepth 40000 in
theorem denseHeadBody_all (c : R2Cfg) :
    c.denseHeadBody.all (ainstrWFB regCount) = true := by
  have hm : c.markBody.all (ainstrWFB regCount) = true := by rfl
  have hc : c.classBody.all (ainstrWFB regCount) = true := by rfl
  have ht : c.tailBody.all (ainstrWFB regCount) = true := by rfl
  unfold R2Cfg.denseHeadBody
  simp only [List.all_append, hm, hc, ht, denseClassSuffix_all,
    denseLogBody_all, Bool.and_true]

theorem r2DenseHeadProgram_wf (c : R2Cfg) (s : R2Seed) :
    (r2DenseHeadProgram c s).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c s),
   forall_wf_of_all (denseHeadBody_all c),
   forall_wf_of_all (epilogue_all c)⟩

/-- CompCert/CCIR correctness bridge for the dense head artifact. -/
theorem r2DenseHeadProgram_compiled (c : R2Cfg) (s : R2Seed) (base : Int)
    (hBase : BaseOk (r2DenseHeadProgram c s).arrayLen base)
    (n : Nat) (hDenote : (r2DenseHeadProgram c s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((r2DenseHeadProgram c s).initialMCC base)
          (r2DenseHeadProgram c s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(r2DenseHeadProgram c s).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (r2DenseHeadProgram_wf c s) base hBase n hDenote

#print axioms r2DenseHeadProgram_wf
#print axioms r2DenseHeadProgram_compiled

end LeanCompCert.Ports.R2SegSieve

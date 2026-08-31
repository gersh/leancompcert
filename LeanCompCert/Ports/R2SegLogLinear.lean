import LeanCompCert.Ports.R2SegLogAccumulator

/-!
# Linear accumulator island in the `R₂*` log phase

The production body advances the linear `2γ` contribution in two small
pieces around its first inequality check.  Keeping those pieces symbolic
prevents Lean from normalizing the complete 42-instruction majorant block.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayScalarBlock (lift)
open LeanCompCert.Verified.InstrBlock

/-- Instructions 286 through the first `rD` commit. -/
def logGapLinearInstrs (g : Nat) : List Instr :=
  [ .binop 286 .sub (.reg rNe) (.reg rPrev)
  , .binop 287 .lt (.reg 286) (.lit 65536)
  , .binop 288 .sub (.lit 1) (.reg 287)
  , .binop 289 .mul (.reg 288) (.reg 247)
  , .binop rViol .add (.reg rViol) (.reg 289)
  , .binop rVGap .add (.reg rVGap) (.reg 289)
  , .binop 290 .sub (.reg 286) (.lit 1)
  , .binop 291 .mul (.reg 290) (.lit g)
  , .binop 292 .mul (.reg 291) (.reg 247)
  , .binop rD .add (.reg rD) (.reg 292) ]

def logGapLinearBody (g : Nat) : List AInstr := lift (logGapLinearInstrs g)

theorem logGapLinearBody_eq_slice (c : R2Cfg) :
    (logBetweenJumpAndCommitBody c).take 10 =
      logGapLinearBody (gammaStep c.sc) := by
  rfl

/-- A finished event advances `rD` from the preceding test point to `n-1`.
Every machine-word side condition is explicit. -/
theorem logGapLinearInstrs_run (k : Nat) (s : RegState)
    (n prev d g : Nat)
    (hne : s rNe = n) (hprev : s rPrev = prev)
    (hd : s rD = d) (hfin : s 247 = 1)
    (hprevn : prev < n) (hnM : n < M) (hgM : g < M)
    (hgap : n - prev < 65536)
    (hprodM : (n - prev - 1) * g < M)
    (haddM : d + (n - prev - 1) * g < M) :
    (srun k s (logGapLinearInstrs g)) rD =
      d + (n - prev - 1) * g := by
  have hsub : denoteOp .sub n prev = some (n - prev) :=
    LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (Nat.le_of_lt hprevn) hnM
  have hsubOne : denoteOp .sub (n - prev) 1 =
      some (n - prev - 1) :=
    LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (by omega) (Nat.lt_trans hgap (by decide))
  have hgapM : n - prev < M := Nat.lt_trans hgap (by decide)
  have h65536M : 65536 < M := by decide
  have hzeroM : 0 < M := by decide
  have honeM : 1 < M := by decide
  simp_all [logGapLinearInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, rNe, rPrev, rD, rViol, rVGap,
    Nat.mod_eq_of_lt]

theorem logGapLinearBody_run (k : Nat) (s : AState)
    (n prev d g : Nat)
    (hne : s.regs rNe = n) (hprev : s.regs rPrev = prev)
    (hd : s.regs rD = d) (hfin : s.regs 247 = 1)
    (hprevn : prev < n) (hnM : n < M) (hgM : g < M)
    (hgap : n - prev < 65536)
    (hprodM : (n - prev - 1) * g < M)
    (haddM : d + (n - prev - 1) * g < M) :
    (arun k s (logGapLinearBody g)).regs rD =
      d + (n - prev - 1) * g := by
  rw [logGapLinearBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logGapLinearInstrs_run k s.regs n prev d g hne hprev hd hfin
    hprevn hnM hgM hgap hprodM haddM

/-- Instructions 293--297 and their two failure-counter commits do not alter
the linear accumulator. -/
def logClauseOneBody (c : R2Cfg) : List AInstr :=
  ((logBetweenJumpAndCommitBody c).drop 10).take 7

/-- The final linear step, instructions 298 and its `rD` commit. -/
def logLastLinearInstrs (g : Nat) : List Instr :=
  [ .binop 298 .mul (.reg 247) (.lit g)
  , .binop rD .add (.reg rD) (.reg 298) ]

def logLastLinearBody (g : Nat) : List AInstr :=
  lift (logLastLinearInstrs g)

theorem logLastLinearBody_eq_slice (c : R2Cfg) :
    ((logBetweenJumpAndCommitBody c).drop 17).take 2 =
      logLastLinearBody (gammaStep c.sc) := by
  rfl

theorem logLastLinearInstrs_run (k : Nat) (s : RegState) (d g : Nat)
    (hfin : s 247 = 1) (hd : s rD = d)
    (hgM : g < M) (haddM : d + g < M) :
    (srun k s (logLastLinearInstrs g)) rD = d + g := by
  have hd' : s 180 = d := by simpa [rD] using hd
  simp [logLastLinearInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, rD, hfin, hd', Nat.mod_eq_of_lt hgM,
    Nat.mod_eq_of_lt haddM]

theorem logLastLinearBody_run (k : Nat) (s : AState) (d g : Nat)
    (hfin : s.regs 247 = 1) (hd : s.regs rD = d)
    (hgM : g < M) (haddM : d + g < M) :
    (arun k s (logLastLinearBody g)).regs rD = d + g := by
  rw [logLastLinearBody,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact logLastLinearInstrs_run k s.regs d g hfin hd hgM haddM

/-- The remaining square-root/log-majorant updates do not alter `rD`. -/
def logAfterLastLinearBody (c : R2Cfg) : List AInstr :=
  (logBetweenJumpAndCommitBody c).drop 19

theorem logBetweenJumpAndCommitBody_eq_linear_stages (c : R2Cfg) :
    logBetweenJumpAndCommitBody c =
      logGapLinearBody (gammaStep c.sc) ++ logClauseOneBody c ++
        logLastLinearBody (gammaStep c.sc) ++
          logAfterLastLinearBody c := by
  rfl

/-- The whole intervening block advances the source linear accumulator from
`prev` to `n`, while its comparison, square-root, and threshold instructions
are treated only through register frames. -/
theorem logBetweenJumpAndCommitBody_linear_run
    (c : R2Cfg) (k : Nat) (s : AState) (n prev d : Nat)
    (hne : s.regs rNe = n) (hprev : s.regs rPrev = prev)
    (hd : s.regs rD = d) (hfin : s.regs 247 = 1)
    (hprevn : prev < n) (hnM : n < M)
    (hgM : gammaStep c.sc < M)
    (hgap : n - prev < 65536)
    (hprodM : (n - prev - 1) * gammaStep c.sc < M)
    (hfirstM : d + (n - prev - 1) * gammaStep c.sc < M)
    (hfinalM : d + (n - prev) * gammaStep c.sc < M) :
    (arun k s (logBetweenJumpAndCommitBody c)).regs rD =
      d + (n - prev) * gammaStep c.sc := by
  let g := gammaStep c.sc
  let afterGap := arun k s (logGapLinearBody g)
  let afterClause := arun k afterGap (logClauseOneBody c)
  let afterLast := arun k afterClause (logLastLinearBody g)
  have hgapRun := logGapLinearBody_run k s n prev d g hne hprev hd hfin
    hprevn hnM hgM hgap hprodM hfirstM
  have hclauseD : afterClause.regs rD = afterGap.regs rD :=
    arun_frame k rD (logClauseOneBody c) (by rfl) afterGap
  have hclauseFin : afterClause.regs 247 = 1 :=
    (arun_frame k 247 (logClauseOneBody c) (by rfl) afterGap).trans
      ((arun_frame k 247 (logGapLinearBody g) (by rfl) s).trans hfin)
  have hcombine :
      d + (n - prev - 1) * g + g = d + (n - prev) * g := by
    have hpos : 0 < n - prev := Nat.sub_pos_of_lt hprevn
    have hsplit : n - prev - 1 + 1 = n - prev :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
    simpa [Nat.add_mul, Nat.add_assoc] using
      congrArg (fun x : Nat => d + x * g) hsplit
  have hlastM : d + (n - prev - 1) * g + g < M := by
    rw [hcombine]
    simpa only [g] using hfinalM
  have hlast := logLastLinearBody_run k afterClause
    (d + (n - prev - 1) * g) g hclauseFin
    (hclauseD.trans hgapRun) hgM hlastM
  have hafter :
      (arun k afterLast (logAfterLastLinearBody c)).regs rD =
        afterLast.regs rD :=
    arun_frame k rD (logAfterLastLinearBody c) (by rfl) afterLast
  rw [logBetweenJumpAndCommitBody_eq_linear_stages,
    arun_append, arun_append, arun_append]
  exact hafter.trans (hlast.trans hcombine)

/-- Composition through the event commit with the post-linear accumulator
derived from the literal program.  This removes the formerly external `d`
hypothesis from `logJumpThroughCommitBody_run`. -/
theorem logJumpThroughCommitBody_linear_run
    (c : R2Cfg) (k : Nat) (s : AState)
    (positive : Bool) (u v e n prev d err terms : Nat)
    (hu : s.regs 272 = u) (hv : s.regs 278 = v)
    (hpositive : s.regs 266 = if positive then 1 else 0)
    (he : s.regs rEx = e) (hfin : s.regs 247 = 1)
    (hne : s.regs rNe = n) (hprev : s.regs rPrev = prev)
    (hd : s.regs rD = d)
    (herr : s.regs rErr = err) (hterms : s.regs rTerms = terms)
    (hS : c.sc < M) (hSm4 : c.sc - 4 < M)
    (hl2 : ln2Up c.sc < M) (huv : u * v < M)
    (hshift : ((u * v) <<< (if positive then 1 else 0)) < M)
    (he1 : e + 1 < M) (henum : (e + 1) * ln2Up c.sc < M)
    (hcharge : ((e + 1) * ln2Up c.sc / 2 ^ (c.sc - 4)) + 2 < M)
    (hprevn : prev < n) (hnM : n < M)
    (hgM : gammaStep c.sc < M) (hgap : n - prev < 65536)
    (hprodM : (n - prev - 1) * gammaStep c.sc < M)
    (hfirstM : d + (n - prev - 1) * gammaStep c.sc < M)
    (hlinearM : d + (n - prev) * gammaStep c.sc < M)
    (hsub : positive = false →
      ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc ≤
        d + (n - prev) * gammaStep c.sc)
    (hdadd : positive = true →
      d + (n - prev) * gammaStep c.sc +
        ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc < M)
    (htermM : ((u * v) <<< (if positive then 1 else 0)) /
      2 ^ c.sc < M)
    (herradd : err +
      (((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2) < M)
    (htermsadd : terms + 1 < M) :
    let linear := d + (n - prev) * gammaStep c.sc
    let term := ((u * v) <<< (if positive then 1 else 0)) / 2 ^ c.sc
    let charge := ((e + 1) * ln2Up c.sc) / 2 ^ (c.sc - 4) + 2
    let out := arun k s
      (logJumpErrorBody c.sc (ln2Up c.sc) ++
        logBetweenJumpAndCommitBody c ++ logUnderflowAuditBody ++
          logAccumulatorCommitBody)
    out.regs rD = (if positive then linear + term else linear - term) ∧
      out.regs rErr = err + charge ∧ out.regs rTerms = terms + 1 ∧
      out.arr = s.arr := by
  let afterJump := arun k s (logJumpErrorBody c.sc (ln2Up c.sc))
  let linear := d + (n - prev) * gammaStep c.sc
  have hne' : afterJump.regs rNe = n :=
    (arun_frame k rNe (logJumpErrorBody c.sc (ln2Up c.sc))
      (by rfl) s).trans hne
  have hprev' : afterJump.regs rPrev = prev :=
    (arun_frame k rPrev (logJumpErrorBody c.sc (ln2Up c.sc))
      (by rfl) s).trans hprev
  have hd' : afterJump.regs rD = d :=
    (arun_frame k rD (logJumpErrorBody c.sc (ln2Up c.sc))
      (by rfl) s).trans hd
  have hfin' : afterJump.regs 247 = 1 :=
    (arun_frame k 247 (logJumpErrorBody c.sc (ln2Up c.sc))
      (by rfl) s).trans hfin
  have hlinear :
      (arun k afterJump (logBetweenJumpAndCommitBody c)).regs rD = linear :=
    logBetweenJumpAndCommitBody_linear_run c k afterJump n prev d
      hne' hprev' hd' hfin' hprevn hnM hgM hgap hprodM hfirstM hlinearM
  have hrun := logJumpThroughCommitBody_run c k s positive u v e linear
    err terms hu hv hpositive he hfin herr hterms hS hSm4 hl2 huv hshift
    he1 henum hcharge hlinear hsub hdadd hlinearM htermM herradd htermsadd
  simpa only [linear] using hrun

#print axioms logGapLinearInstrs_run
#print axioms logBetweenJumpAndCommitBody_linear_run
#print axioms logJumpThroughCommitBody_linear_run

end LeanCompCert.Ports.R2SegSieve

import LeanCompCert.Verified.Frontend

/-!
# Straight-line SSA blocks over the expression front end

`Verified/Frontend.lean` compiles one expression into fresh temporaries and
proves it correct.  Programs of any size are built by *sequencing* many
such assignments, and doing that by hand — threading frame conditions
through every step — does not scale past a few dozen instructions.

This module adds the missing composition layer.  An `Assign` is "register
`dest` gets the value of `expr`"; a block is a list of them, compiled by
reusing one temporary cursor for every assignment.  The payoff is
`block_correct`: running the compiled block agrees, on every register below
the cursor, with the *total* `Nat`-level function `run`, which is an
ordinary left fold of `RegState.set`.  Reasoning about a 30 000-instruction
body therefore never unfolds a single instruction: block specifications
compose through `run_append` and `run_congr`.

Totality is bought by excluding division: `NoDiv` expressions have no
`udiv`/`urem` node, so their denotation is never `none` and `evalExpr` is a
plain `Nat` function.  Montgomery arithmetic needs no division, which is
exactly why this layer suffices for it.
-/

namespace LeanCompCert.Verified.Straight

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend

/-! ## Total evaluation of division-free expressions -/

/-- Total evaluation, agreeing with `denoteExpr` on division-free
expressions. -/
def evalExpr (k : Nat) (s : RegState) : Expr → Nat
  | .reg i => s i
  | .lit v => v % M
  | .idx => k % M
  | .bin op l r => (denoteOp op (evalExpr k s l) (evalExpr k s r)).getD 0

/-- The expression contains no `udiv`/`urem` node. -/
def NoDiv : Expr → Bool
  | .reg _ => true
  | .lit _ => true
  | .idx => true
  | .bin op l r =>
      (op != Op.udiv) && (op != Op.urem) && NoDiv l && NoDiv r

/-- Away from `udiv`/`urem`, `denoteOp` never fails. -/
private theorem denoteOp_isSome (op : Op) (h1 : op ≠ Op.udiv)
    (h2 : op ≠ Op.urem) (a b : Nat) :
    denoteOp op a b = some ((denoteOp op a b).getD 0) := by
  cases op
  case udiv => exact absurd rfl h1
  case urem => exact absurd rfl h2
  all_goals rfl

/-- Destructing `NoDiv` at a binary node. -/
private theorem noDiv_bin {op : Op} {l r : Expr}
    (h : NoDiv (.bin op l r) = true) :
    op ≠ Op.udiv ∧ op ≠ Op.urem ∧ NoDiv l = true ∧ NoDiv r = true := by
  revert h
  cases op <;> simp [NoDiv]

/-- On division-free expressions the partial denotation is total, and
equal to `evalExpr`. -/
theorem denoteExpr_eq_evalExpr (k : Nat) (s : RegState) :
    ∀ e : Expr, NoDiv e = true → denoteExpr k s e = some (evalExpr k s e) := by
  intro e
  induction e with
  | reg i => intro _; rfl
  | lit v => intro _; rfl
  | «idx» => intro _; rfl
  | bin op l r ihl ihr =>
      intro h
      obtain ⟨h1, h2, hl, hr⟩ := noDiv_bin h
      show (denoteExpr k s l).bind
          (fun a => (denoteExpr k s r).bind fun b => denoteOp op a b) = _
      rw [ihl hl, ihr hr]
      exact denoteOp_isSome op h1 h2 _ _

/-- Every value `evalExpr` produces is a `u64`. -/
theorem evalExpr_lt (k : Nat) (s : RegState)
    (hs : ∀ i, s i < M) :
    ∀ e : Expr, NoDiv e = true → evalExpr k s e < M := by
  intro e
  induction e with
  | reg i => intro _; exact hs i
  | lit v => intro _; exact Nat.mod_lt _ M_pos
  | «idx» => intro _; exact Nat.mod_lt _ M_pos
  | bin op l r _ _ =>
      intro h
      obtain ⟨h1, h2, _, _⟩ := noDiv_bin h
      show (denoteOp op (evalExpr k s l) (evalExpr k s r)).getD 0 < M
      exact denoteOp_lt op (evalExpr k s l) (evalExpr k s r) _
        (denoteOp_isSome op h1 h2 (evalExpr k s l) (evalExpr k s r))

/-- The evaluation only reads registers the expression mentions. -/
theorem evalExpr_congr {c : Nat} {s t : RegState}
    (hAgree : ∀ i, i < c → s i = t i) (k : Nat) :
    ∀ e : Expr, e.RegsBelow c → evalExpr k s e = evalExpr k t e := by
  intro e
  induction e with
  | reg i => intro h; exact hAgree i h
  | lit v => intro _; rfl
  | «idx» => intro _; rfl
  | bin op l r ihl ihr =>
      intro h
      show (denoteOp op (evalExpr k s l) (evalExpr k s r)).getD 0 = _
      rw [ihl h.1, ihr h.2]
      rfl

/-! ## Temporary budget -/

/-- Number of temporaries `compileExpr` consumes. -/
def depth : Expr → Nat
  | .reg _ => 1
  | .lit _ => 1
  | .idx => 1
  | .bin _ l r => depth l + depth r + 1

theorem compileExpr_cursor_eq (e : Expr) :
    ∀ cursor : Nat, (compileExpr cursor e).2.2 = cursor + depth e := by
  induction e with
  | reg i => intro c; rfl
  | lit v => intro c; rfl
  | «idx» => intro c; rfl
  | bin op l r ihl ihr =>
      intro c
      show (compileExpr (compileExpr c l).2.2 r).2.2 + 1 =
        c + (depth l + depth r + 1)
      rw [ihr (compileExpr c l).2.2, ihl c]
      omega

/-- Every instruction `compileExpr` emits addresses registers below the
final cursor. -/
theorem compileExpr_wf (e : Expr) :
    ∀ (cursor bound : Nat), e.RegsBelow cursor → cursor + depth e ≤ bound →
      ∀ i ∈ (compileExpr cursor e).1, i.WF bound := by
  induction e with
  | reg j =>
      intro cursor bound hFresh hRoom i hi
      have hb : cursor < bound := hRoom
      have hi' : i ∈ [Instr.mov cursor (.reg j)] := hi
      simp only [List.mem_singleton] at hi'
      subst hi'
      exact ⟨hb, Nat.lt_trans hFresh hb⟩
  | lit v =>
      intro cursor bound _ hRoom i hi
      have hb : cursor < bound := hRoom
      have hi' : i ∈ [Instr.mov cursor (.lit v)] := hi
      simp only [List.mem_singleton] at hi'
      subst hi'
      exact ⟨hb, trivial⟩
  | «idx» =>
      intro cursor bound _ hRoom i hi
      have hb : cursor < bound := hRoom
      have hi' : i ∈ [Instr.mov cursor .idx] := hi
      simp only [List.mem_singleton] at hi'
      subst hi'
      exact ⟨hb, trivial⟩
  | bin op l r ihl ihr =>
      intro cursor bound hFresh hRoom i hi
      obtain ⟨hFl, hFr⟩ := hFresh
      have hRoom' : cursor + (depth l + depth r + 1) ≤ bound := hRoom
      have hdl : (compileExpr cursor l).2.2 = cursor + depth l :=
        compileExpr_cursor_eq l cursor
      have hdr : (compileExpr (compileExpr cursor l).2.2 r).2.2 =
          (compileExpr cursor l).2.2 + depth r :=
        compileExpr_cursor_eq r _
      have hL : cursor + depth l ≤ bound := by omega
      have hR : (compileExpr cursor l).2.2 + depth r ≤ bound := by omega
      have hDestLt : (compileExpr (compileExpr cursor l).2.2 r).2.2 < bound := by
        omega
      have hFr' : r.RegsBelow (compileExpr cursor l).2.2 :=
        Expr.RegsBelow.mono (compileExpr_cursor_le l cursor) r hFr
      have hi' : i ∈ (compileExpr cursor l).1 ++
          (compileExpr (compileExpr cursor l).2.2 r).1 ++
          [Instr.binop (compileExpr (compileExpr cursor l).2.2 r).2.2 op
            (.reg (compileExpr cursor l).2.1)
            (.reg (compileExpr (compileExpr cursor l).2.2 r).2.1)] := hi
      rcases List.mem_append.mp hi' with h | h
      · rcases List.mem_append.mp h with h | h
        · exact ihl cursor bound hFl hL i h
        · exact ihr (compileExpr cursor l).2.2 bound hFr' hR i h
      · simp only [List.mem_singleton] at h
        subst h
        refine ⟨hDestLt, ?_, ?_⟩
        · show (compileExpr cursor l).2.1 < bound
          have := compileExpr_result_lt l cursor
          omega
        · show (compileExpr (compileExpr cursor l).2.2 r).2.1 < bound
          have := compileExpr_result_lt r (compileExpr cursor l).2.2
          omega

/-! ## Assignments and blocks -/

/-- One straight-line assignment: `dest := expr`. -/
structure Assign where
  dest : Nat
  expr : Expr
  deriving Repr

/-- The instructions of one assignment, using temporaries from `cursor`. -/
def Assign.instrs (cursor : Nat) (a : Assign) : List Instr :=
  a.expr.toBody a.dest cursor

/-- A block: assignments in order, all sharing one temporary cursor. -/
def block (cursor : Nat) (as : List Assign) : List Instr :=
  as.flatMap (Assign.instrs cursor)

/-- The `Nat`-level meaning of a block: a fold of `RegState.set`. -/
def run (k : Nat) (s : RegState) : List Assign → RegState
  | [] => s
  | a :: rest => run k (s.set a.dest (evalExpr k s a.expr)) rest

/-- Well-formed assignment: writes below the cursor, reads below the
cursor, and is division-free. -/
def Assign.WF (cursor : Nat) (a : Assign) : Prop :=
  a.dest < cursor ∧ a.expr.RegsBelow cursor ∧ NoDiv a.expr = true

/-- Two register files agree on everything the block can see. -/
def AgreeBelow (cursor : Nat) (s t : RegState) : Prop :=
  ∀ r, r < cursor → s r = t r

theorem AgreeBelow.refl (cursor : Nat) (s : RegState) : AgreeBelow cursor s s :=
  fun _ _ => rfl

/-! ## Sequencing -/

private theorem set_self (s : RegState) (i v : Nat) : (s.set i v) i = v := by
  simp [RegState.set]

private theorem set_ne (s : RegState) (i v j : Nat) (h : j ≠ i) :
    (s.set i v) j = s j := by
  simp [RegState.set, h]

private theorem block_cons (cursor : Nat) (a : Assign) (rest : List Assign) :
    block cursor (a :: rest) =
      a.expr.toBody a.dest cursor ++ block cursor rest := rfl

theorem block_append (cursor : Nat) (as bs : List Assign) :
    block cursor (as ++ bs) = block cursor as ++ block cursor bs := by
  simp [block, List.flatMap_append]

theorem run_append (k : Nat) (as bs : List Assign) :
    ∀ s : RegState, run k s (as ++ bs) = run k (run k s as) bs := by
  induction as with
  | nil => intro s; rfl
  | cons a rest ih =>
      intro s
      exact ih (s.set a.dest (evalExpr k s a.expr))

/-- Running a block only depends on the registers below the cursor. -/
theorem run_congr (k cursor : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) :
    ∀ s t : RegState, AgreeBelow cursor s t →
      AgreeBelow cursor (run k s as) (run k t as) := by
  induction as with
  | nil => intro s t h; exact h
  | cons a rest ih =>
      intro s t hAgree
      have ha : a.WF cursor := hWF a (by simp)
      have hrest : ∀ b ∈ rest, b.WF cursor := fun b hb => hWF b (by simp [hb])
      have hval : evalExpr k s a.expr = evalExpr k t a.expr :=
        evalExpr_congr hAgree k a.expr ha.2.1
      show AgreeBelow cursor (run k (s.set a.dest (evalExpr k s a.expr)) rest)
        (run k (t.set a.dest (evalExpr k t a.expr)) rest)
      refine ih hrest _ _ ?_
      intro r hr
      by_cases hEq : r = a.dest
      · subst hEq
        rw [set_self, set_self]
        exact hval
      · rw [set_ne _ _ _ _ hEq, set_ne _ _ _ _ hEq]
        exact hAgree r hr

/-! ## The correctness theorem -/

/--
**Block correctness.**  The compiled straight-line block runs to
completion, and the register file it produces agrees, below the cursor,
with the total `Nat`-level fold `run`.

Every hypothesis is per-assignment, so the theorem costs the same at three
assignments and at thirty thousand.
-/
theorem block_correct (k cursor : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) :
    ∀ s : RegState, ∃ s',
      denoteInstrs k s (block cursor as) = some s' ∧
        AgreeBelow cursor s' (run k s as) := by
  induction as with
  | nil => intro s; exact ⟨s, rfl, AgreeBelow.refl cursor s⟩
  | cons a rest ih =>
      intro s
      have ha : a.WF cursor := hWF a (by simp)
      have hrest : ∀ b ∈ rest, b.WF cursor := fun b hb => hWF b (by simp [hb])
      obtain ⟨hdest, hregs, hnodiv⟩ := ha
      have hden : denoteExpr k s a.expr = some (evalExpr k s a.expr) :=
        denoteExpr_eq_evalExpr k s a.expr hnodiv
      obtain ⟨s1, h1, h1v, h1f⟩ :=
        Expr.toBody_correct a.expr a.dest cursor hregs k s _ hden
      obtain ⟨s2, h2, h2a⟩ := ih hrest s1
      refine ⟨s2, ?_, ?_⟩
      · rw [block_cons, denoteInstrs_append, h1]
        exact h2
      · have hAB : AgreeBelow cursor s1 (s.set a.dest (evalExpr k s a.expr)) := by
          intro r hr
          by_cases hEq : r = a.dest
          · subst hEq
            rw [set_self]
            exact h1v
          · rw [set_ne _ _ _ _ hEq]
            exact h1f r hr hEq
        have hRun := run_congr k cursor rest hrest s1 _ hAB
        show AgreeBelow cursor s2
          (run k (s.set a.dest (evalExpr k s a.expr)) rest)
        intro r hr
        exact (h2a r hr).trans (hRun r hr)

/-- Every instruction of a compiled block is well-formed for a machine
with `regCount` registers, provided the temporaries fit. -/
theorem block_wf (cursor regCount : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) (hcur : cursor ≤ regCount)
    (hroom : ∀ a ∈ as, cursor + depth a.expr ≤ regCount) :
    ∀ i ∈ block cursor as, i.WF regCount := by
  induction as with
  | nil => intro i hi; simp [block] at hi
  | cons a rest ih =>
      intro i hi
      have ha : a.WF cursor := hWF a (by simp)
      have hroa : cursor + depth a.expr ≤ regCount := hroom a (by simp)
      have hrest : ∀ b ∈ rest, b.WF cursor := fun b hb => hWF b (by simp [hb])
      have hroomrest : ∀ b ∈ rest, cursor + depth b.expr ≤ regCount :=
        fun b hb => hroom b (by simp [hb])
      have hi' : i ∈ ((compileExpr cursor a.expr).1 ++
          [Instr.mov a.dest (.reg (compileExpr cursor a.expr).2.1)]) ++
          block cursor rest := hi
      rcases List.mem_append.mp hi' with h | h
      · rcases List.mem_append.mp h with h | h
        · exact compileExpr_wf a.expr cursor regCount ha.2.1 hroa i h
        · simp only [List.mem_singleton] at h
          subst h
          refine ⟨Nat.lt_of_lt_of_le ha.1 hcur, ?_⟩
          show (compileExpr cursor a.expr).2.1 < regCount
          have h1 := compileExpr_result_lt a.expr cursor
          have h2 := compileExpr_cursor_eq a.expr cursor
          omega
      · exact ih hrest hroomrest i h

/-! ## Reading the result of a fold -/

/-- Registers not written by the block keep their value. -/
theorem run_untouched (k : Nat) (as : List Assign) (r : Nat)
    (hr : ∀ a ∈ as, a.dest ≠ r) :
    ∀ s : RegState, run k s as r = s r := by
  induction as with
  | nil => intro s; rfl
  | cons a rest ih =>
      intro s
      have hne : a.dest ≠ r := hr a (by simp)
      have hrest : ∀ b ∈ rest, b.dest ≠ r := fun b hb => hr b (by simp [hb])
      show run k (s.set a.dest (evalExpr k s a.expr)) rest r = s r
      rw [ih hrest, set_ne _ _ _ _ (Ne.symm hne)]

/-- Every register a block writes stays a `u64`, and untouched registers
keep whatever bound they had. -/
theorem run_lt (k cursor : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) :
    ∀ s : RegState, (∀ i, s i < M) → ∀ i, run k s as i < M := by
  induction as with
  | nil => intro s hs i; exact hs i
  | cons a rest ih =>
      intro s hs
      have ha : a.WF cursor := hWF a (by simp)
      have hrest : ∀ b ∈ rest, b.WF cursor := fun b hb => hWF b (by simp [hb])
      show ∀ i, run k (s.set a.dest (evalExpr k s a.expr)) rest i < M
      refine ih hrest _ ?_
      intro i
      by_cases hEq : i = a.dest
      · subst hEq
        rw [set_self]
        exact evalExpr_lt k s hs a.expr ha.2.2
      · rw [set_ne _ _ _ _ hEq]
        exact hs i

end LeanCompCert.Verified.Straight

import LeanCompCert.Verified.Reflect

/-!
# A verified expression front end for the register DSL

Step functions for the reflection bridge (`LeanCompCert.Verified.Reflect`)
are written as three-address `Instr` lists, which is tedious and
error-prone. This module adds an **expression layer**: a small expression
AST (`Expr`), its denotation (`denoteExpr`) mirroring the `u64` semantics of
`denoteOp`/`denoteOperand` exactly, and a naive fresh-temp compiler
(`compileExpr`) into `Instr` lists, together with a once-and-for-all
correctness theorem (`compileExpr_correct`):

- running the compiled instructions from any state agrees with the
  expression's denotation (including divergence on division by zero), and
- every register below the initial fresh-temp cursor is left untouched
  (the frame condition), so compiled expressions can be dropped into
  loop bodies without clobbering program state.

`Expr.toBody` packages a compiled expression as a body fragment that moves
the result into a chosen destination register (`Expr.toBody_correct`).
-/

namespace LeanCompCert.Verified.Frontend

open LeanCompCert.Verified.Reflect

/-! ## Expressions and their denotation -/

/-- Expressions over registers, `u64` literals, and the loop index. -/
inductive Expr where
  | reg (i : Nat)
  | lit (v : Nat)
  | idx
  | bin (op : Op) (lhs rhs : Expr)
  deriving Repr, DecidableEq

/-- Denotation of an expression at loop index `k` in register state `s`,
mirroring `denoteOperand`/`denoteOp` exactly: `u64` semantics, with
division and remainder by zero undefined. -/
def denoteExpr (k : Nat) (s : RegState) : Expr → Option Nat
  | .reg i => some (s i)
  | .lit v => some (v % M)
  | .idx => some (k % M)
  | .bin op lhs rhs =>
      (denoteExpr k s lhs).bind fun a =>
        (denoteExpr k s rhs).bind fun b =>
          denoteOp op a b

/-- Every register mentioned in the expression lies below `cursor`. -/
def Expr.RegsBelow (cursor : Nat) : Expr → Prop
  | .reg i => i < cursor
  | .lit _ => True
  | .idx => True
  | .bin _ lhs rhs => lhs.RegsBelow cursor ∧ rhs.RegsBelow cursor

theorem Expr.RegsBelow.mono {c c' : Nat} (hle : c ≤ c') :
    ∀ e : Expr, e.RegsBelow c → e.RegsBelow c' := by
  intro e
  induction e with
  | reg i => exact fun h => Nat.lt_of_lt_of_le h hle
  | lit v => exact fun _ => trivial
  | idx => exact fun _ => trivial
  | bin op l r ihl ihr => exact fun h => ⟨ihl h.1, ihr h.2⟩

/-- The denotation only reads registers mentioned in the expression. -/
theorem denoteExpr_congr {c : Nat} {s s' : RegState}
    (hAgree : ∀ i, i < c → s i = s' i) (k : Nat) :
    ∀ e : Expr, e.RegsBelow c → denoteExpr k s e = denoteExpr k s' e := by
  intro e
  induction e with
  | reg i =>
      intro h
      simp only [denoteExpr]
      rw [hAgree i h]
  | lit v => intro _; rfl
  | idx => intro _; rfl
  | bin op l r ihl ihr =>
      intro h
      simp only [denoteExpr]
      rw [ihl h.1, ihr h.2]

/-! ## The compiler -/

/--
Naive fresh-temp compilation: `cursor` is the next free register.
Returns `(instructions, result register, new cursor)`. Leaves compile to a
`mov` into a fresh register; a binary node compiles both subtrees and then
issues one `binop` into a fresh register.
-/
def compileExpr (cursor : Nat) : Expr → List Instr × Nat × Nat
  | .reg i => ([.mov cursor (.reg i)], cursor, cursor + 1)
  | .lit v => ([.mov cursor (.lit v)], cursor, cursor + 1)
  | .idx => ([.mov cursor .idx], cursor, cursor + 1)
  | .bin op lhs rhs =>
      let cl := compileExpr cursor lhs
      let cr := compileExpr cl.2.2 rhs
      (cl.1 ++ cr.1 ++ [.binop cr.2.2 op (.reg cl.2.1) (.reg cr.2.1)],
        cr.2.2, cr.2.2 + 1)

private theorem compileExpr_bin_instrs (cursor : Nat) (op : Op)
    (lhs rhs : Expr) :
    (compileExpr cursor (.bin op lhs rhs)).1 =
      (compileExpr cursor lhs).1 ++
        (compileExpr (compileExpr cursor lhs).2.2 rhs).1 ++
        [.binop (compileExpr (compileExpr cursor lhs).2.2 rhs).2.2 op
          (.reg (compileExpr cursor lhs).2.1)
          (.reg (compileExpr (compileExpr cursor lhs).2.2 rhs).2.1)] := rfl

private theorem compileExpr_bin_res (cursor : Nat) (op : Op)
    (lhs rhs : Expr) :
    (compileExpr cursor (.bin op lhs rhs)).2.1 =
      (compileExpr (compileExpr cursor lhs).2.2 rhs).2.2 := rfl

private theorem compileExpr_bin_cursor (cursor : Nat) (op : Op)
    (lhs rhs : Expr) :
    (compileExpr cursor (.bin op lhs rhs)).2.2 =
      (compileExpr (compileExpr cursor lhs).2.2 rhs).2.2 + 1 := rfl

/-- The cursor never decreases. -/
theorem compileExpr_cursor_le (e : Expr) :
    ∀ cursor : Nat, cursor ≤ (compileExpr cursor e).2.2 := by
  induction e with
  | reg i => intro c; exact Nat.le_succ c
  | lit v => intro c; exact Nat.le_succ c
  | idx => intro c; exact Nat.le_succ c
  | bin op l r ihl ihr =>
      intro c
      rw [compileExpr_bin_cursor]
      exact Nat.le_trans (ihl c) (Nat.le_trans (ihr _) (Nat.le_succ _))

/-- The result register is below the new cursor. -/
theorem compileExpr_result_lt (e : Expr) :
    ∀ cursor : Nat, (compileExpr cursor e).2.1 < (compileExpr cursor e).2.2 := by
  induction e with
  | reg i => intro c; exact Nat.lt_succ_self c
  | lit v => intro c; exact Nat.lt_succ_self c
  | idx => intro c; exact Nat.lt_succ_self c
  | bin op l r ihl ihr =>
      intro c
      rw [compileExpr_bin_res, compileExpr_bin_cursor]
      exact Nat.lt_succ_self _

/-! ## Option-bind and `denoteInstrs` reduction lemmas -/

private theorem obind_none {α β : Type _} (f : α → Option β) :
    (none : Option α).bind f = none := rfl

private theorem obind_some {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

private theorem denoteInstrs_cons (k : Nat) (s : RegState) (instr : Instr)
    (rest : List Instr) :
    denoteInstrs k s (instr :: rest) =
      (denoteInstr k s instr).bind fun s' => denoteInstrs k s' rest := rfl

/-- Sequencing lemma: running an appended instruction list is the
`Option.bind` of running the two halves. -/
theorem denoteInstrs_append (k : Nat) (xs ys : List Instr) :
    ∀ s : RegState, denoteInstrs k s (xs ++ ys) =
      (denoteInstrs k s xs).bind fun s' => denoteInstrs k s' ys := by
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih =>
      intro s
      rw [List.cons_append, denoteInstrs_cons, denoteInstrs_cons]
      cases denoteInstr k s x with
      | none => rfl
      | some s1 =>
          simp only [obind_some]
          exact ih s1

private theorem denoteInstrs_singleton (k : Nat) (s : RegState)
    (instr : Instr) :
    denoteInstrs k s [instr] = denoteInstr k s instr := by
  rw [denoteInstrs_cons]
  cases denoteInstr k s instr with
  | none => rfl
  | some s' => rfl

private theorem denoteInstr_binop (k : Nat) (s : RegState) (dest : Nat)
    (op : Op) (lop rop : Operand) :
    denoteInstr k s (.binop dest op lop rop) =
      (denoteOp op (denoteOperand k s lop) (denoteOperand k s rop)).bind
        fun result => some (s.set dest result) := rfl

/-! ## Compiler correctness -/

/--
**Soundness, defined case**: if the expression denotes `v`, running the
compiled instructions from any state `s` succeeds, leaves `v` in the result
register, and touches no register below the initial cursor.
-/
theorem compileExpr_sound (e : Expr) :
    ∀ cursor : Nat, e.RegsBelow cursor →
    ∀ (k : Nat) (s : RegState) (v : Nat), denoteExpr k s e = some v →
    ∃ s', denoteInstrs k s (compileExpr cursor e).1 = some s' ∧
      s' (compileExpr cursor e).2.1 = v ∧ ∀ r, r < cursor → s' r = s r := by
  induction e with
  | reg i =>
      intro cursor _ k s v hDenote
      simp only [denoteExpr, Option.some.injEq] at hDenote
      subst hDenote
      refine ⟨s.set cursor (s i), rfl, ?_, ?_⟩
      · show (s.set cursor (s i)) cursor = s i
        simp [RegState.set]
      · intro r hr
        simp [RegState.set, Nat.ne_of_lt hr]
  | lit n =>
      intro cursor _ k s v hDenote
      simp only [denoteExpr, Option.some.injEq] at hDenote
      subst hDenote
      refine ⟨s.set cursor (n % M), rfl, ?_, ?_⟩
      · show (s.set cursor (n % M)) cursor = n % M
        simp [RegState.set]
      · intro r hr
        simp [RegState.set, Nat.ne_of_lt hr]
  | idx =>
      intro cursor _ k s v hDenote
      simp only [denoteExpr, Option.some.injEq] at hDenote
      subst hDenote
      refine ⟨s.set cursor (k % M), rfl, ?_, ?_⟩
      · show (s.set cursor (k % M)) cursor = k % M
        simp [RegState.set]
      · intro r hr
        simp [RegState.set, Nat.ne_of_lt hr]
  | bin op l r ihl ihr =>
      intro cursor hFresh k s v hDenote
      obtain ⟨hFl, hFr⟩ := hFresh
      simp only [denoteExpr] at hDenote
      cases hl : denoteExpr k s l with
      | none =>
          simp only [hl, obind_none] at hDenote
          cases hDenote
      | some a =>
          simp only [hl, obind_some] at hDenote
          cases hr : denoteExpr k s r with
          | none =>
              simp only [hr, obind_none] at hDenote
              cases hDenote
          | some b =>
              simp only [hr, obind_some] at hDenote
              obtain ⟨s1, h1, h1v, h1f⟩ := ihl cursor hFl k s a hl
              have hFr' : r.RegsBelow (compileExpr cursor l).2.2 :=
                Expr.RegsBelow.mono (compileExpr_cursor_le l cursor) r hFr
              have hr1 : denoteExpr k s1 r = some b := by
                rw [denoteExpr_congr h1f k r hFr]
                exact hr
              obtain ⟨s2, h2, h2v, h2f⟩ :=
                ihr (compileExpr cursor l).2.2 hFr' k s1 b hr1
              have hs2a : s2 (compileExpr cursor l).2.1 = a := by
                rw [h2f _ (compileExpr_result_lt l cursor), h1v]
              simp only [compileExpr_bin_instrs, compileExpr_bin_res]
              refine ⟨s2.set (compileExpr (compileExpr cursor l).2.2 r).2.2 v,
                ?_, ?_, ?_⟩
              · rw [denoteInstrs_append, denoteInstrs_append, h1]
                simp only [obind_some]
                rw [h2]
                simp only [obind_some]
                rw [denoteInstrs_singleton, denoteInstr_binop]
                simp only [denoteOperand]
                rw [hs2a, h2v, hDenote]
                simp only [obind_some]
              · simp [RegState.set]
              · intro rr hrr
                have hlt : rr < (compileExpr (compileExpr cursor l).2.2 r).2.2 :=
                  Nat.lt_of_lt_of_le hrr
                    (Nat.le_trans (compileExpr_cursor_le l cursor)
                      (compileExpr_cursor_le r (compileExpr cursor l).2.2))
                simp only [RegState.set, if_neg (Nat.ne_of_lt hlt)]
                rw [h2f rr (Nat.lt_of_lt_of_le hrr
                    (compileExpr_cursor_le l cursor)),
                  h1f rr hrr]

/--
**Soundness, undefined case**: if the expression's denotation is undefined
(division or remainder by zero), running the compiled instructions is also
undefined.
-/
theorem compileExpr_none (e : Expr) :
    ∀ cursor : Nat, e.RegsBelow cursor →
    ∀ (k : Nat) (s : RegState), denoteExpr k s e = none →
    denoteInstrs k s (compileExpr cursor e).1 = none := by
  induction e with
  | reg i =>
      intro cursor _ k s hDenote
      simp only [denoteExpr] at hDenote
      cases hDenote
  | lit n =>
      intro cursor _ k s hDenote
      simp only [denoteExpr] at hDenote
      cases hDenote
  | idx =>
      intro cursor _ k s hDenote
      simp only [denoteExpr] at hDenote
      cases hDenote
  | bin op l r ihl ihr =>
      intro cursor hFresh k s hDenote
      obtain ⟨hFl, hFr⟩ := hFresh
      simp only [denoteExpr] at hDenote
      simp only [compileExpr_bin_instrs]
      rw [denoteInstrs_append, denoteInstrs_append]
      cases hl : denoteExpr k s l with
      | none =>
          simp only [ihl cursor hFl k s hl, obind_none]
      | some a =>
          simp only [hl, obind_some] at hDenote
          obtain ⟨s1, h1, h1v, h1f⟩ := compileExpr_sound l cursor hFl k s a hl
          rw [h1]
          simp only [obind_some]
          have hFr' : r.RegsBelow (compileExpr cursor l).2.2 :=
            Expr.RegsBelow.mono (compileExpr_cursor_le l cursor) r hFr
          cases hr : denoteExpr k s r with
          | none =>
              have hr1 : denoteExpr k s1 r = none := by
                rw [denoteExpr_congr h1f k r hFr]
                exact hr
              simp only [ihr (compileExpr cursor l).2.2 hFr' k s1 hr1,
                obind_none]
          | some b =>
              simp only [hr, obind_some] at hDenote
              have hr1 : denoteExpr k s1 r = some b := by
                rw [denoteExpr_congr h1f k r hFr]
                exact hr
              obtain ⟨s2, h2, h2v, h2f⟩ :=
                compileExpr_sound r (compileExpr cursor l).2.2 hFr' k s1 b hr1
              have hs2a : s2 (compileExpr cursor l).2.1 = a := by
                rw [h2f _ (compileExpr_result_lt l cursor), h1v]
              rw [h2]
              simp only [obind_some]
              rw [denoteInstrs_singleton, denoteInstr_binop]
              simp only [denoteOperand]
              rw [hs2a, h2v, hDenote]
              simp only [obind_none]

/--
**Compiler correctness**: running the compiled instructions from any state
agrees with `denoteExpr` — divergence maps to divergence, and a defined
value `v` maps to a successful run leaving `v` in the result register with
every register below the initial cursor untouched.
-/
theorem compileExpr_correct (e : Expr) (cursor : Nat)
    (hFresh : e.RegsBelow cursor) (k : Nat) (s : RegState) :
    match denoteExpr k s e with
    | none => denoteInstrs k s (compileExpr cursor e).1 = none
    | some v => ∃ s', denoteInstrs k s (compileExpr cursor e).1 = some s' ∧
        s' (compileExpr cursor e).2.1 = v ∧ ∀ r, r < cursor → s' r = s r := by
  cases hDenote : denoteExpr k s e with
  | none => exact compileExpr_none e cursor hFresh k s hDenote
  | some v => exact compileExpr_sound e cursor hFresh k s v hDenote

/-! ## The body builder -/

/--
Package a compiled expression as a body fragment: evaluate `e` using fresh
temporaries at `cursor` and above, then move the result into `dest`.
-/
def Expr.toBody (dest cursor : Nat) (e : Expr) : List Instr :=
  (compileExpr cursor e).1 ++ [.mov dest (.reg (compileExpr cursor e).2.1)]

/--
Running `e.toBody dest cursor` from any state sets `dest` to the value of
`e` and preserves every other register below `cursor`.
-/
theorem Expr.toBody_correct (e : Expr) (dest cursor : Nat)
    (hFresh : e.RegsBelow cursor) (k : Nat) (s : RegState) (v : Nat)
    (hDenote : denoteExpr k s e = some v) :
    ∃ s', denoteInstrs k s (e.toBody dest cursor) = some s' ∧
      s' dest = v ∧ ∀ r, r < cursor → r ≠ dest → s' r = s r := by
  obtain ⟨s1, h1, h1v, h1f⟩ := compileExpr_sound e cursor hFresh k s v hDenote
  refine ⟨s1.set dest (s1 (compileExpr cursor e).2.1), ?_, ?_, ?_⟩
  · unfold Expr.toBody
    rw [denoteInstrs_append, h1]
    simp only [obind_some]
    rfl
  · simpa [RegState.set] using h1v
  · intro rr hrr hne
    simp only [RegState.set, if_neg hne]
    exact h1f rr hrr

/-- If the expression's denotation is undefined, so is its body fragment. -/
theorem Expr.toBody_none (e : Expr) (dest cursor : Nat)
    (hFresh : e.RegsBelow cursor) (k : Nat) (s : RegState)
    (hDenote : denoteExpr k s e = none) :
    denoteInstrs k s (e.toBody dest cursor) = none := by
  unfold Expr.toBody
  rw [denoteInstrs_append]
  simp only [compileExpr_none e cursor hFresh k s hDenote, obind_none]

/-! ## Surface syntax: the `expr!( … )` macro

Purely syntactic sugar reifying a small expression surface syntax into
`Expr` values — no proof obligations. Registers are written `# n`,
numeric literals denote `Expr.lit`, and `idx` is the loop index.
-/

declare_syntax_cat frontendExpr

syntax:max "#" num : frontendExpr
syntax:max num : frontendExpr
-- ⚠ The loop index token is `@idx`, not `idx`.  Lean's token table is GLOBAL:
-- registering a bare identifier here would stop `idx` being usable as an
-- identifier in EVERY module that transitively imports this one.  A consumer
-- binding `(idx : Nat → Nat)` then fails to parse, far from any mention of
-- this package.  Every other token in this category is a non-identifier
-- symbol (`#`, `+`, `==`, …) and is therefore safe; keep it that way.
syntax:max "@idx" : frontendExpr
syntax:max "(" frontendExpr ")" : frontendExpr
syntax:65 frontendExpr:65 " + " frontendExpr:66 : frontendExpr
syntax:65 frontendExpr:65 " - " frontendExpr:66 : frontendExpr
syntax:70 frontendExpr:70 " * " frontendExpr:71 : frontendExpr
syntax:70 frontendExpr:70 " / " frontendExpr:71 : frontendExpr
syntax:70 frontendExpr:70 " % " frontendExpr:71 : frontendExpr
syntax:50 frontendExpr:51 " == " frontendExpr:51 : frontendExpr
syntax:50 frontendExpr:51 " != " frontendExpr:51 : frontendExpr
syntax:50 frontendExpr:51 " < " frontendExpr:51 : frontendExpr
syntax:50 frontendExpr:51 " <= " frontendExpr:51 : frontendExpr
syntax:50 frontendExpr:51 " > " frontendExpr:51 : frontendExpr
syntax:50 frontendExpr:51 " >= " frontendExpr:51 : frontendExpr

/-- Reify the surface syntax into an `Expr` value. -/
syntax "expr!(" frontendExpr ")" : term

macro_rules
  | `(expr!(# $n)) => `(Expr.reg $n)
  | `(expr!($n:num)) => `(Expr.lit $n)
  | `(expr!(@idx)) => `(Expr.idx)
  | `(expr!(($a))) => `(expr!($a))
  | `(expr!($a + $b)) => `(Expr.bin Op.add expr!($a) expr!($b))
  | `(expr!($a - $b)) => `(Expr.bin Op.sub expr!($a) expr!($b))
  | `(expr!($a * $b)) => `(Expr.bin Op.mul expr!($a) expr!($b))
  | `(expr!($a / $b)) => `(Expr.bin Op.udiv expr!($a) expr!($b))
  | `(expr!($a % $b)) => `(Expr.bin Op.urem expr!($a) expr!($b))
  | `(expr!($a == $b)) => `(Expr.bin Op.eq expr!($a) expr!($b))
  | `(expr!($a != $b)) => `(Expr.bin Op.ne expr!($a) expr!($b))
  | `(expr!($a < $b)) => `(Expr.bin Op.lt expr!($a) expr!($b))
  | `(expr!($a <= $b)) => `(Expr.bin Op.le expr!($a) expr!($b))
  | `(expr!($a > $b)) => `(Expr.bin Op.gt expr!($a) expr!($b))
  | `(expr!($a >= $b)) => `(Expr.bin Op.ge expr!($a) expr!($b))

example :
    expr!(# 0 + 5 * @idx) =
      Expr.bin .add (.reg 0) (.bin .mul (.lit 5) .idx) := rfl

example :
    expr!((# 1 + # 2) < 10) =
      Expr.bin .lt (.bin .add (.reg 1) (.reg 2)) (.lit 10) := rfl

example : denoteExpr 0 (fun _ => 0) expr!(2 + 3) = some 5 := rfl

example : denoteExpr 0 (fun _ => 0) expr!(2 / 0) = none := rfl

end LeanCompCert.Verified.Frontend

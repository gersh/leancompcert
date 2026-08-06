import LeanCompCert.Ports.Section413Sweep

/-!
# Kernel-efficient Section 4.13 head/main evaluator

Lean's kernel reduces `Array` through lists, making random update linear in
the array length.  This module changes only that representation: accumulator
slots live in a low-bit binary trie, so read and write take a fixed number of
constructor steps.  `Section413HMTrieSound` proves the trie sweep agrees with
the independent array model in `Section413Sweep`.
-/

namespace LeanCompCert.Ports.Section413HMTrie

open LeanCompCert.Ports.Section413Sweep

inductive Trie (α : Type) where
  | empty
  | leaf (value : α)
  | node (left right : Trie α)
  deriving Repr, DecidableEq

namespace Trie

variable {α : Type}

def left : Trie α → Trie α
  | .empty => .empty
  | .leaf x => .leaf x
  | .node l _ => l

def right : Trie α → Trie α
  | .empty => .empty
  | .leaf x => .leaf x
  | .node _ r => r

def get [Inhabited α] : Trie α → List Bool → α
  | .empty, _ => default
  | .leaf x, _ => x
  | .node _ _, [] => default
  | .node l r, b :: bs => if b then get r bs else get l bs

def set : Trie α → List Bool → α → Trie α
  | _, [], x => .leaf x
  | t, b :: bs, x =>
      if b then .node t.left (set t.right bs x)
      else .node (set t.left bs x) t.right

end Trie

def bits (width index : Nat) : List Bool :=
  (List.range width).map (fun j => index.testBit j)

def getN {α : Type} [Inhabited α] (width : Nat) (t : Trie α) (index : Nat) : α :=
  t.get (bits width index)

def setN {α : Type} (width : Nat) (t : Trie α) (index : Nat) (x : α) : Trie α :=
  t.set (bits width index) x

def touch (width R : Nat) (w : Cell) (p : Trie Cell × Cell) (d : Nat) :
    Trie Cell × Cell :=
  let A := getN width p.1 d
  (setN width p.1 d (cadd A w), cadd p.2 (deltaTerm (muZ d R) A w))

def stepDivisors (width R X : Nat) (w : Cell) (st : Trie Cell × Cell) :
    Trie Cell × Cell :=
  (List.range (Nat.sqrt X)).foldl
    (fun p i =>
      let r := i + 1
      if X % r = 0 then
        let p1 := touch width R w p r
        if X / r ≠ r then touch width R w p1 (X / r) else p1
      else p) st

structure State where
  acc : Trie Cell
  g : Cell
  headAcc : Int
  mainAcc : Int
  deriving Repr, DecidableEq

def step (width R : Nat) (w : Cell) (s : State) (X : Nat) : State :=
  let ad := stepDivisors width R X w (s.acc, czero)
  let g' := cadd s.g ad.2
  { acc := ad.1, g := g',
    headAcc := s.headAcc + cabsUB g' * ((5 * X * X + 2 * X + 1 : Nat) : Int),
    mainAcc := s.mainAcc + mainTermUB X g' }

def initial : State := ⟨Trie.empty, czero, 0, 0⟩

/-- Execute `count` candidates beginning with `start + 1`. -/
def advance (width v R start count : Nat) (s : State) : State :=
  (List.range count).foldl
    (fun s i =>
      let X := start + i + 1
      step width R (if v = 2 then weightV2 R X else weightV1 R X) s X) s

def run (width v R N : Nat) : State :=
  advance width v R 0 N initial

theorem advance_succ (width v R start count : Nat) (s : State) :
    advance width v R start (count + 1) s =
      step width R
        (if v = 2 then weightV2 R (start + count + 1)
          else weightV1 R (start + count + 1))
        (advance width v R start count s) (start + count + 1) := by
  simp [advance, List.range_succ, List.foldl_append]

theorem advance_add (width v R start a b : Nat) (s : State) :
    advance width v R start (a + b) s =
      advance width v R (start + a) b (advance width v R start a s) := by
  induction b with
  | zero => simp [advance]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        advance_succ, ih, advance_succ]
      rw [show start + (a + b) + 1 = start + a + b + 1 by omega]

def v1OK (width R N : Nat) : Bool :=
  let s := run width 1 R N
  decide (s.headAcc ≤ 37224400 * (SCALE : Int)) &&
    decide (10000000 * s.mainAcc ≤ 2 * 3624829 * (SCALE : Int))

def v2OK (width R N : Nat) : Bool :=
  let s := run width 2 R N
  decide (s.headAcc ≤ 47734021 * (SCALE : Int)) &&
    decide (10000000 * s.mainAcc ≤ 4 * 3605763 * (SCALE : Int))

def productionOK : Bool := v1OK 14 999 10000 && v2OK 14 999 10000

end LeanCompCert.Ports.Section413HMTrie

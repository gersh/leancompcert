import LeanCompCert.Ports.RamareMStar140MRound
import LeanCompCert.Ports.BlockedFold

/-!
# `MSEncoding`, discharged: the `m★` program denotes `msRef`

`Ports/RamareMStar140MRound.lean` says what **one flat round** does.  This
module re-blocks `len · B` of them into `len` candidates
(`Ports/BlockedFold.lean`), identifies one block with `msStep`, runs the
initialization block, and assembles the three through
`ArrayFoldBridge.AProgram.denote_eq_obs_foldl_mem`.

★ The observation carries the **array**, which is what distinguishes this port
from `Ports/RamareWM217.lean` (whose array is read-only).  The one fact that
makes the re-blocking work is `msRound_arr_indep`: a round never reads the
cell its own candidate is about to write, so the value stored there by earlier
rounds of the same block — the *previous* candidate's packed cell — is invisible.
That is exactly why the body can afford an unconditional `store`.
-/

namespace LeanCompCert.Ports.RamareMStar140M

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.BlockedFold
open LeanCompCert.Verified.InstrBlock
  (srun sval sdest SDefined SAllDefined NoDivI srun_append SAllDefined_append)

/-! ## The candidate-level view of a round state -/

/-- A round state, forgetting the three registers a candidate consumes. -/
def toSt (st : RSt) : St :=
  { bad := st.bad, lb := st.lb, lam := st.lam, idx := st.idx, bs := st.bs
  , mx := st.mx, cell := st.cell, arr := st.arr }

/-- What holds at every block boundary: every carried quantity is a word, and
the log slot is in the table. -/
def BInv (c : Cfg) (st : RSt) : Prop :=
  st.bad < M ∧ st.lb < M ∧ st.lam < M ∧ st.idx < c.tab ∧ st.bs < M ∧
    st.mx < M ∧ st.cell < M ∧ st.acc < M ∧ st.sc < M ∧ st.muQ < M ∧
    (∀ i, st.arr i < M)

/-! ## The store is invisible inside its own block -/

/--
**A round does not see the cell its own candidate is about to write.**

Every read index is `⌊n/w²⌋ ≤ n/4`, or `q = n/p ≤ n/2`, or a log cell above
`limit` — never `n` itself.  So overwriting cell `n` with anything at all
leaves the round unchanged, which is what lets the block's earlier rounds
store the *previous* candidate's packed cell there without being observed.
-/
theorem msRound_arr_indep (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (st : RSt) (hidx : st.idx < c.tab) (v : Nat) :
    msRound c k { st with arr := fun j => if j = c.n0 + k / c.B then v else st.arr j }
      = msRound c k st := by
  sorry

/-- **The boundary invariant is preserved by a round.** -/
theorem msRound_BInv (c : Cfg) (hok : msOK c = true) (k : Nat)
    (hk : k < c.len * c.B) (st : RSt) (h : BInv c st) : BInv c (msRound c k st) := by
  sorry

/-! ## One block of `B` rounds is one candidate -/

/--
**The re-blocking, at one block.**  The statement mentions no problem size.

Rounds `r < B − 2` carry the trial scan and the `w`-terms (`workFold`), round
`B − 2` latches `μ(q)`, round `B − 1` commits — and the three registers a
candidate consumes (`rAcc`, `rS`, `rMuQ`) are cleared or overwritten inside
the block, so the incoming values are irrelevant and `toSt` is enough.
-/
theorem block_eq_msStep (c : Cfg) (hok : msOK c = true) (q : Nat) (hq : q < c.len)
    (st : RSt) (h : BInv c st) :
    toSt (block c.B (fun x r => msRound c r x) st q)
      = msStep c (c.n0 + q) (toSt st) := by
  sorry

/-! ## The initialization block -/

/-- The state the initialization block reaches. -/
def msEntryA (c : Cfg) : AState := arun 0 initialAState (msInit c)

theorem msInit_reaches (c : Cfg) (hok : msOK c = true) :
    denoteAInstrs (c.limit + 1 + c.tab) 0 initialAState (msInit c)
      = some (msEntryA c) := by
  sorry

/-- **The entry state is `msEntry`**: the carried registers, the packed cell
for `q = 1`, and the 69 log constants. -/
theorem msEntry_obs (c : Cfg) (hok : msOK c = true) :
    toSt (obsR (msEntryA c)) = msEntry c ∧
      (obsR (msEntryA c)).acc = 0 ∧ (obsR (msEntryA c)).sc = 0 := by
  sorry

theorem msEntry_inv (c : Cfg) (hok : msOK c = true) :
    MSInv c (msEntryA c) ∧ BInv c (obsR (msEntryA c)) := by
  sorry

/-! ## The whole loop, folded -/

/-- **The flat round fold is the reference.**  `BlockedFold.foldl_range_mul`
re-associates the `len · B` applications into `len` blocks; `block_eq_msStep`
identifies one block.  No fold is evaluated. -/
theorem foldl_msRound_eq_msRef (c : Cfg) (hok : msOK c = true) :
    ((List.range (c.len * c.B)).foldl (fun x r => msRound c r x)
      (obsR (msEntryA c))).bad = msRef c := by
  sorry

/-! ## The encoding obligation, discharged -/

/-- **The program denotes the candidate-level reference.** -/
theorem msProgram_denote (c : Cfg) (hok : msOK c = true) :
    (msProgram c).denote = some (msRef c) := by
  sorry

/-- **`MSEncoding`, proved.** -/
theorem msEncoding (c : Cfg) : MSEncoding c := fun hok => msProgram_denote c hok

end LeanCompCert.Ports.RamareMStar140M

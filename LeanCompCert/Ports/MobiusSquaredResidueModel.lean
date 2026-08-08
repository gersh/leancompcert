import LeanCompCert.Ports.ArraySegMobiusSquaredTotal

/-!
# Transparent model of the squared production Möbius residue

The production replacement keeps sections (A)--(E) of `mobiusLiveResidue`
and changes only the violation update.  This module records that change as a
small `Nat` model.  In particular, the old accumulator and ceiling invariants
can be reused without restating their arithmetic.
-/

namespace LeanCompCert.Ports.MobiusSquaredResidueRealisation

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.MobiusResidueRealisation

/-- The rounded-up allowance used by the root-free endpoint test. -/
def squaredUpper (k n absV : Nat) : Nat :=
  absV + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1

/-- The exact paper-faithful endpoint predicate. -/
abbrev SquaredPass (k n absV : Nat) : Prop :=
  (n + 1) * (squaredUpper k n absV) ^ 2 ≤ 2 ^ 122

/-- Literal word-level violation update of the new section (F). -/
def squaredViolStep (k n absV gate viol : Nat) : Nat :=
  (viol + (if SquaredPass k n absV then 0 else 1) * gate) % M

/-- One residue step with the original accumulator/absolute-value/ceiling
sections and the new squared violation test. -/
def squaredResStep (k : Nat) (g : Sig) (r : Res) : Res :=
  let w := wPair k g.n
  let t := accStep g.pos g.neg w.1 w.2 r.tLo r.tHi
  let a := absBias (vBias k t.1 t.2)
  let c := celStep g.n r.celSq r.cel g.gate
  ⟨t.1, t.2, c.1, c.2, squaredViolStep k g.n a g.gate r.viol⟩

/-- The first four persistent fields are definitionally unchanged. -/
theorem squaredResStep_prefix (k : Nat) (g : Sig) (r : Res) :
    let old := resStep k g r
    let new := squaredResStep k g r
    new.tLo = old.tLo ∧ new.tHi = old.tHi ∧
      new.cel = old.cel ∧ new.celSq = old.celSq := by
  simp [squaredResStep, resStep]

/-- The violation field exposes exactly the squared predicate. -/
theorem squaredResStep_viol (k : Nat) (g : Sig) (r : Res) :
    (squaredResStep k g r).viol =
      squaredViolStep k g.n
        (absBias (vBias k
          (accStep g.pos g.neg (wPair k g.n).1 (wPair k g.n).2
            r.tLo r.tHi).1
          (accStep g.pos g.neg (wPair k g.n).1 (wPair k g.n).2
            r.tLo r.tHi).2))
        g.gate r.viol := by
  rfl

end LeanCompCert.Ports.MobiusSquaredResidueRealisation

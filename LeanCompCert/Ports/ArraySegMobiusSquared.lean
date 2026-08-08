import LeanCompCert.Ports.ArraySegSieve

/-!
# Production segmented-sieve residue for the root-free Möbius test

This is the paper-faithful production alternative to
`ArraySegSieve.mobiusLiveResidue`.  It reuses that residue's first 42
instructions (sections (A)--(E)), so the exact fixed-point accumulator,
absolute value, and ceiling carry fields are unchanged.  Only section (F) is
replaced by the finite predicate

`(n + 1) * (absV + ceil(n / 2^(k+2)) + 1)^2 <= 2^122`.

The product is evaluated by three literal half-limb multipliers and a
three-word comparison.  No square root, division, `native_decide`, or closed
Boolean carrier is used for the endpoint test.
-/

namespace LeanCompCert.Ports.ArraySegSieve

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-! Registers `165`--`191` are scratch for this residue.  They overlap the
Mertens-live residue's scratch/class registers, but the two residues are
alternative suffixes and never occur in the same program. -/

/-- The literal half-limb `u64 x u64 -> (lo, hi)` circuit modeled by
`Verified.MulWide.hl`. -/
def mobiusSquaredWideBody
    (ra rb rlo rhi s0 s1 s2 s3 s4 s5 s6 s7 : Nat) : List AInstr :=
  [ .scalar (.binop s0 .band (.reg ra) (.lit 4294967295))
  , .scalar (.binop s1 .lshr (.reg ra) (.lit 32))
  , .scalar (.binop s2 .band (.reg rb) (.lit 4294967295))
  , .scalar (.binop s3 .lshr (.reg rb) (.lit 32))
  , .scalar (.binop s4 .mul (.reg s0) (.reg s2))
  , .scalar (.binop s5 .mul (.reg s0) (.reg s3))
  , .scalar (.binop s6 .mul (.reg s1) (.reg s2))
  , .scalar (.binop s7 .mul (.reg s1) (.reg s3))
  , .scalar (.binop s0 .add (.reg s5) (.reg s6))
  , .scalar (.binop s1 .lt (.reg s0) (.reg s5))
  , .scalar (.binop s2 .shl (.reg s0) (.lit 32))
  , .scalar (.binop rlo .add (.reg s4) (.reg s2))
  , .scalar (.binop s3 .lt (.reg rlo) (.reg s4))
  , .scalar (.binop s5 .lshr (.reg s0) (.lit 32))
  , .scalar (.binop s6 .mul (.reg s1) (.lit 4294967296))
  , .scalar (.binop rhi .add (.reg s7) (.reg s5))
  , .scalar (.binop rhi .add (.reg rhi) (.reg s6))
  , .scalar (.binop rhi .add (.reg rhi) (.reg s3)) ]

/-- Exact squared section (F).  On entry, register `159` is `absV`, register
`65` is `n`, and register `133` is the main-accumulation gate. -/
def mobiusSquaredTestBody (k : Nat) : List AInstr :=
  [ .scalar (.binop 165 .add (.reg 65) (.lit (2 ^ (k + 2) - 1)))
  , .scalar (.binop 165 .lshr (.reg 165) (.lit (k + 2)))
  , .scalar (.binop 166 .add (.reg 159) (.reg 165))
  , .scalar (.binop 166 .add (.reg 166) (.lit 1))
  , .scalar (.binop 167 .add (.reg 65) (.lit 1))
  ] ++
  mobiusSquaredWideBody 166 166 168 169 177 178 179 180 181 182 183 184 ++
  mobiusSquaredWideBody 168 167 170 171 177 178 179 180 181 182 183 184 ++
  mobiusSquaredWideBody 169 167 172 173 177 178 179 180 181 182 183 184 ++
  [ .scalar (.binop 174 .add (.reg 171) (.reg 172))
  , .scalar (.binop 175 .lt (.reg 174) (.reg 172))
  , .scalar (.binop 176 .add (.reg 173) (.reg 175))
  , .scalar (.binop 185 .ne (.reg 176) (.lit 0))
  , .scalar (.binop 186 .gt (.reg 174) (.lit (2 ^ 58)))
  , .scalar (.binop 187 .eq (.reg 174) (.lit (2 ^ 58)))
  , .scalar (.binop 188 .ne (.reg 170) (.lit 0))
  , .scalar (.binop 189 .mul (.reg 187) (.reg 188))
  , .scalar (.binop 190 .bor (.reg 185) (.reg 186))
  , .scalar (.binop 191 .bor (.reg 190) (.reg 189))
  , .scalar (.binop 177 .mul (.reg 191) (.reg 133))
  , .scalar (.binop rMViol .add (.reg rMViol) (.reg 177)) ]

/-- Production accumulator/absolute-value/ceiling prefix plus the exact
squared endpoint test. -/
def mobiusLiveSquaredResidue (k : Nat) : List AInstr :=
  (mobiusLiveResidue k).take 42 ++ mobiusSquaredTestBody k

/-- Production segmented-sieve program using the root-free squared predicate
at every gated integer. -/
def mobiusLiveSquaredProgram (c : Cfg) (k : Nat) (s : MobLiveSeed) : AProgram :=
  c.program (mobiusLiveSquaredResidue k) (mobiusLiveInit s) (mobiusLiveEpilogue c)

theorem mobiusLiveSquaredResidue_all (k : Nat) :
    (mobiusLiveSquaredResidue k).all (ainstrWFB regCount) = true := by
  rfl

theorem mobiusLiveSquaredProgram_wf (c : Cfg) (k : Nat) (s : MobLiveSeed) :
    (mobiusLiveSquaredProgram c k s).WF :=
  segProgram_wf c (mobiusLiveSquaredResidue_all k) (mobiusLiveInit_all s)
    (mobiusLiveEpilogue_all c)

/-- Compiler bridge for the production root-free squared residue. -/
theorem mobiusLiveSquaredProgram_compiled (c : Cfg) (k : Nat) (s : MobLiveSeed)
    (base : Int)
    (hBase : BaseOk (mobiusLiveSquaredProgram c k s).arrayLen base)
    (n : Nat) (hDenote : (mobiusLiveSquaredProgram c k s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((mobiusLiveSquaredProgram c k s).initialMCC base)
          (mobiusLiveSquaredProgram c k s).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(mobiusLiveSquaredProgram c k s).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (mobiusLiveSquaredProgram_wf c k s) base hBase
    n hDenote

end LeanCompCert.Ports.ArraySegSieve

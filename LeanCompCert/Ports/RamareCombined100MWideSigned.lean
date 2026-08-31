import LeanCompCert.Ports.AddWidePort
import LeanCompCert.Ports.Section413Cells
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Ports.ArraySegSieve

/-!
# Reusable signed two-limb accumulation

The Ramaré row endpoints exceed one signed machine word, although each single
candidate increment fits.  This module gives the array machine a reusable
`i64 -> i128` sign extension followed by the already-verified two-limb add.
It is purely symbolic: no production sweep is evaluated here.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WideSigned

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock

abbrev B64 : Nat := LeanCompCert.Verified.AddWide.B64
abbrev B128 : Nat := LeanCompCert.Verified.AddWide.B128

def encodeZ128 (z : Int) : Nat := (z % (B128 : Int)).toNat

def rep (lo hi : Nat) (z : Int) : Prop :=
  LeanCompCert.Verified.AddWide.wval (lo, hi) = encodeZ128 z

/-- Canonical low limb of a signed integer's `2^128` encoding. -/
def loOf (z : Int) : Nat := encodeZ128 z % B64

/-- Canonical high limb of a signed integer's `2^128` encoding. -/
def hiOf (z : Int) : Nat := encodeZ128 z / B64

theorem encodeZ128_lt (z : Int) : encodeZ128 z < B128 := by
  simp only [encodeZ128, B128, LeanCompCert.Verified.AddWide.B128]
  omega

theorem encodeZ128_add (a b : Int) :
    (encodeZ128 a + encodeZ128 b) % B128 = encodeZ128 (a + b) := by
  simp only [encodeZ128, B128, LeanCompCert.Verified.AddWide.B128]
  omega

theorem loOf_lt (z : Int) : loOf z < B64 := by
  exact Nat.mod_lt _ LeanCompCert.Verified.AddWide.B64_pos

theorem hiOf_lt (z : Int) : hiOf z < B64 := by
  have hz := encodeZ128_lt z
  simp only [hiOf, B128, B64, LeanCompCert.Verified.AddWide.B128,
    LeanCompCert.Verified.AddWide.B64, LeanCompCert.Verified.MulWide.B64] at hz ⊢
  omega

/-- Splitting the canonical encoding gives a canonical representing pair.
This is used to seed persistent accumulators from a mathematical prefix state,
instead of silently starting the suffix at zero. -/
theorem loOf_hiOf_rep (z : Int) : rep (loOf z) (hiOf z) z := by
  unfold rep loOf hiOf LeanCompCert.Verified.AddWide.wval
  have hB : 0 < B64 := LeanCompCert.Verified.AddWide.B64_pos
  have hsplit := Nat.mod_add_div (encodeZ128 z) B64
  omega

/-- A valid limb pair representing the canonical residue is unique. -/
theorem rep_eq_canonical {lo hi : Nat} (z : Int)
    (hlo : lo < B64) (hrep : rep lo hi z) :
    lo = loOf z ∧ hi = hiOf z := by
  have hc := loOf_hiOf_rep z
  have hclo := loOf_lt z
  have hchi := hiOf_lt z
  simp only [rep, LeanCompCert.Verified.AddWide.wval, B64,
    LeanCompCert.Verified.AddWide.B64,
    LeanCompCert.Verified.MulWide.B64] at hrep hc hlo hclo hchi
  constructor <;> omega

/-- High limb of the sign extension of one two's-complement word. -/
def signHi (w : Nat) : Nat := if Section413Cells.H63 ≤ w then B64 - 1 else 0

/-- Materialize the high sign-extension limb in two instructions. -/
def signExtendBlock (dstHi src sign : Nat) : List AInstr :=
  [ .scalar (.binop sign .ge (.reg src) (.lit Section413Cells.H63))
  , .scalar (.binop dstHi .sub (.lit 0) (.reg sign)) ]

theorem subWideABody_run (k : Nat) (s : AState)
    (lo hi carry alo ahi : Nat)
    (hregs : LeanCompCert.Ports.AddWidePort.WideRegs lo hi carry alo ahi) :
    let out := arun k s
      (LeanCompCert.Ports.AddWidePort.subWideABody lo hi carry alo ahi)
    (out.regs lo, out.regs hi) =
      LeanCompCert.Verified.AddWide.subWide
        (s.regs lo, s.regs hi) (s.regs alo, s.regs ahi) := by
  dsimp only
  change
    ((arun k s (LeanCompCert.Verified.ArrayScalarBlock.lift
        (LeanCompCert.Ports.AddWidePort.subWideBody lo hi carry alo ahi))).regs lo,
      (arun k s (LeanCompCert.Verified.ArrayScalarBlock.lift
        (LeanCompCert.Ports.AddWidePort.subWideBody lo hi carry alo ahi))).regs hi) = _
  rw [LeanCompCert.Verified.ArrayScalarBlock.arun_lift_regs]
  exact (LeanCompCert.Ports.AddWidePort.subWideBody_run
    lo hi carry alo ahi k hregs s.regs).1

theorem signExtendBlock_run (k : Nat) (s : AState) (dstHi src sign : Nat) :
    (arun k s (signExtendBlock dstHi src sign)).regs dstHi = signHi (s.regs src) := by
  simp only [signExtendBlock, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg]
  have hH : Section413Cells.H63 % M = Section413Cells.H63 := by decide
  simp only [if_true, Option.getD_some, Nat.zero_mod, hH]
  by_cases h : Section413Cells.H63 ≤ s.regs src
  · rw [if_pos h]
    simp only [signHi, h, if_true]
    rw [LeanCompCert.Ports.AddWidePort.M_eq_B64]
    exact Nat.mod_eq_of_lt (by decide)
  · rw [if_neg h]
    simp [signHi, h]

theorem signExtendBlock_src_frame (k : Nat) (s : AState)
    (dstHi src sign : Nat) (h1 : src ≠ dstHi) (h2 : src ≠ sign) :
    (arun k s (signExtendBlock dstHi src sign)).regs src = s.regs src :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by
    simp [LeanCompCert.Verified.ArrayRegFrame.writes,
      LeanCompCert.Verified.ArrayRegFrame.instrWrites,
      LeanCompCert.Verified.InstrBlock.sdest, signExtendBlock,
      Ne.symm h1, Ne.symm h2]) _

/-- Add a signed one-word increment to a two-limb two's-complement value. -/
def addSigned64Block
    (lo hi src ext sign carry : Nat) : List AInstr :=
  signExtendBlock ext src sign ++
    LeanCompCert.Ports.AddWidePort.addWideABody lo hi carry src ext

theorem addSigned64Block_run (k : Nat) (s : AState)
    (lo hi src ext sign carry : Nat)
    (hregs : LeanCompCert.Ports.AddWidePort.WideRegs lo hi carry src ext)
    (hsrcExt : src ≠ ext) (hsrcSign : src ≠ sign)
    (hloSign : lo ≠ sign)
    (hhiSign : hi ≠ sign) :
    let out := arun k s (addSigned64Block lo hi src ext sign carry)
    (out.regs lo, out.regs hi) =
      LeanCompCert.Verified.AddWide.addWide
        (s.regs lo, s.regs hi) (s.regs src, signHi (s.regs src)) := by
  dsimp only
  rw [addSigned64Block, arun_append]
  let staged := arun k s (signExtendBlock ext src sign)
  have hext : staged.regs ext = signHi (s.regs src) :=
    signExtendBlock_run k s ext src sign
  have hsrc : staged.regs src = s.regs src :=
    signExtendBlock_src_frame k s ext src sign hsrcExt hsrcSign
  have hlo : staged.regs lo = s.regs lo :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by
      rcases hregs with ⟨hlohi, hloc, _hhic, hsrclo, _hsrchi, hsrcc,
        helo, _hehi, hec⟩
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, signExtendBlock,
        helo, Ne.symm hloSign]) _
  have hhi : staged.regs hi = s.regs hi :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame _ _ _ (by
      rcases hregs with ⟨hlohi, _hloc, hhic, _hsrclo, hsrchi, _hsrcc,
        _helo, hehi, _hec⟩
      simp [LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, signExtendBlock,
        hehi, Ne.symm hhiSign]) _
  change ((arun k staged (LeanCompCert.Verified.ArrayScalarBlock.lift
    (LeanCompCert.Ports.AddWidePort.addWideBody lo hi carry src ext))).regs lo,
    (arun k staged (LeanCompCert.Verified.ArrayScalarBlock.lift
      (LeanCompCert.Ports.AddWidePort.addWideBody lo hi carry src ext))).regs hi) = _
  rw [LeanCompCert.Verified.ArrayScalarBlock.arun_lift_regs]
  have hnodiv : ∀ i ∈ LeanCompCert.Ports.AddWidePort.addWideBody
      lo hi carry src ext, LeanCompCert.Verified.InstrBlock.NoDivI i = true := by
    intro i hiMem
    simp only [LeanCompCert.Ports.AddWidePort.addWideBody, List.mem_cons,
      List.not_mem_nil, or_false] at hiMem
    rcases hiMem with rfl | rfl | rfl | rfl <;> rfl
  have hm := LeanCompCert.Verified.InstrBlock.srun_correct k _ hnodiv staged.regs
  obtain ⟨s', hd, hlo', hhi', _hf⟩ :=
    LeanCompCert.Ports.AddWidePort.addWideBody_denote
      lo hi carry src ext hregs k staged.regs
  have heq : s' = LeanCompCert.Verified.InstrBlock.srun k staged.regs
      (LeanCompCert.Ports.AddWidePort.addWideBody lo hi carry src ext) := by
    apply Option.some.inj
    exact hd.symm.trans hm
  subst s'
  have hadd :
      (LeanCompCert.Verified.InstrBlock.srun k staged.regs
          (LeanCompCert.Ports.AddWidePort.addWideBody lo hi carry src ext) lo,
        LeanCompCert.Verified.InstrBlock.srun k staged.regs
          (LeanCompCert.Ports.AddWidePort.addWideBody lo hi carry src ext) hi) =
        LeanCompCert.Verified.AddWide.addWide
          (staged.regs lo, staged.regs hi) (staged.regs src, staged.regs ext) := by
    apply Prod.ext
    · exact hlo'
    · exact hhi'
  simpa only [hlo, hhi, hsrc, hext] using hadd

theorem signHi_encodeZ (z : Int)
    (hzLo : -(Section413Cells.H63 : Int) ≤ z)
    (hzHi : z < (Section413Cells.H63 : Int)) :
    signHi (Section413Cells.encodeZ z) =
      (if z < 0 then B64 - 1 else 0) := by
  unfold signHi
  have hs := Section413Cells.encodeZ_sign z hzLo hzHi
  by_cases hz : z < 0
  · have hw : Section413Cells.H63 ≤ Section413Cells.encodeZ z := hs.mpr hz
    simp [hz, hw]
  · have hw : ¬Section413Cells.H63 ≤ Section413Cells.encodeZ z :=
      fun h => hz (hs.mp h)
    simp [hz, hw]

/-- A signed 64-bit word together with its sign-extension limb represents the
same integer modulo `2^128`. -/
theorem signExtended_rep (z : Int)
    (hzLo : -(Section413Cells.H63 : Int) ≤ z)
    (hzHi : z < (Section413Cells.H63 : Int)) :
    rep (Section413Cells.encodeZ z) (signHi (Section413Cells.encodeZ z)) z := by
  simp only [rep, LeanCompCert.Verified.AddWide.wval, encodeZ128, signHi,
    Section413Cells.encodeZ, Section413Cells.H63, B64, B128,
    LeanCompCert.Verified.AddWide.B64, LeanCompCert.Verified.AddWide.B128,
    LeanCompCert.Verified.MulWide.B64] at *
  split <;> omega

/-- The machine block preserves the signed two-limb representation under
ordinary integer addition. -/
theorem addSigned64Block_rep (k : Nat) (s : AState)
    (lo hi src ext sign carry : Nat) (acc inc : Int)
    (hregs : LeanCompCert.Ports.AddWidePort.WideRegs lo hi carry src ext)
    (hsrcExt : src ≠ ext) (hsrcSign : src ≠ sign)
    (hloSign : lo ≠ sign) (hhiSign : hi ≠ sign)
    (hloM : s.regs lo < M) (hhiM : s.regs hi < M)
    (hrep : rep (s.regs lo) (s.regs hi) acc)
    (hsrc : s.regs src = Section413Cells.encodeZ inc)
    (hincLo : -(Section413Cells.H63 : Int) ≤ inc)
    (hincHi : inc < (Section413Cells.H63 : Int)) :
    let out := arun k s (addSigned64Block lo hi src ext sign carry)
    rep (out.regs lo) (out.regs hi) (acc + inc) := by
  dsimp only
  have hrun := addSigned64Block_run k s lo hi src ext sign carry hregs
    hsrcExt hsrcSign hloSign hhiSign
  have hx : LeanCompCert.Verified.AddWide.Ok (s.regs lo, s.regs hi) := by
    rw [LeanCompCert.Ports.AddWidePort.M_eq_B64] at hloM hhiM
    exact ⟨hloM, hhiM⟩
  have ha : LeanCompCert.Verified.AddWide.Ok
      (s.regs src, signHi (s.regs src)) := by
    rw [hsrc]
    constructor
    · exact Section413Cells.encodeZ_lt inc
    · rw [signHi_encodeZ inc hincLo hincHi]
      split <;> simp only [B64, LeanCompCert.Verified.AddWide.B64,
        LeanCompCert.Verified.MulWide.B64] <;> omega
  unfold rep
  rw [hrun, LeanCompCert.Verified.AddWide.addWide_spec _ _ hx ha, hrep]
  have hincRep := signExtended_rep inc hincLo hincHi
  unfold rep at hincRep
  rw [hsrc, hincRep, encodeZ128_add]

theorem addSigned64Block_wf (regCount lo hi src ext sign carry : Nat)
    (hlo : lo < regCount) (hhi : hi < regCount) (hsrc : src < regCount)
    (hext : ext < regCount) (hsign : sign < regCount)
    (hcarry : carry < regCount) :
    (addSigned64Block lo hi src ext sign carry).all
      (LeanCompCert.Ports.ArraySegSieve.ainstrWFB regCount) = true := by
  simp [addSigned64Block, signExtendBlock,
    LeanCompCert.Ports.AddWidePort.addWideABody,
    LeanCompCert.Ports.AddWidePort.addWideBody,
    LeanCompCert.Ports.ArraySegSieve.ainstrWFB,
    LeanCompCert.Ports.ArraySegSieve.instrWFB,
    LeanCompCert.Ports.ArraySegSieve.operandWFB,
    hlo, hhi, hsrc, hext, hsign, hcarry]

end LeanCompCert.Ports.RamareCombined100M.WideSigned

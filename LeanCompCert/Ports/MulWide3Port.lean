import LeanCompCert.Ports.CDEMAbelPrimitives
import LeanCompCert.Verified.MulWide3

/-!
# CompCert-C block for two-limb by one-word multiplication

This is the machine refinement used by the RS62 §3.14 guard.  Two invocations
of the already verified half-limb multiplier produce the partial products;
three scalar instructions join their middle limbs and carry.  Production
ranges are never evaluated in this file.
-/

namespace LeanCompCert.Ports.MulWide3Port

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports

def rXLo : Nat := 0
def rXHi : Nat := 1
def rY : Nat := 2
def rLo : Nat := 3
def rMid0 : Nat := 4
def rMid1 : Nat := 5
def rTop0 : Nat := 6
def rMid : Nat := 7
def rCarry : Nat := 8
def rTop : Nat := 9
def s0 : Nat := 10
def s1 : Nat := 11
def s2 : Nat := 12
def s3 : Nat := 13
def s4 : Nat := 14
def s5 : Nat := 15
def s6 : Nat := 16
def s7 : Nat := 17
def regCount : Nat := 18

def wide (ra rb lo hi : Nat) : List Instr :=
  Section413G1Denote.mulWideG 4294967295 4294967296
    ra rb lo hi s0 s1 s2 s3 s4 s5 s6 s7

def mulPrefix : List Instr :=
  wide rXLo rY rLo rMid0 ++ wide rXHi rY rMid1 rTop0

def combine : List Instr :=
  [ .binop rMid .add (.reg rMid0) (.reg rMid1)
  , .binop rCarry .lt (.reg rMid) (.reg rMid0)
  , .binop rTop .add (.reg rTop0) (.reg rCarry) ]

def bodyG : List Instr := mulPrefix ++ combine
def body : List AInstr := lift bodyG

def program (xlo xhi y outReg : Nat) : AProgram := {
  regCount := regCount
  arrayLen := 1
  loopCount := 0
  init := lift
    [ .mov rXLo (.lit xlo), .mov rXHi (.lit xhi), .mov rY (.lit y) ] ++ body
  body := []
  epilogue := []
  output := outReg
}

set_option maxRecDepth 40000 in
theorem program_wf (xlo xhi y outReg : Nat) (hout : outReg < regCount) :
    (program xlo xhi y outReg).WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change outReg < regCount
    exact hout
  · exact ArraySegSieve.forall_wf_of_all (by rfl)
  · exact ArraySegSieve.forall_wf_of_all (by rfl)
  · exact ArraySegSieve.forall_wf_of_all (by rfl)

private theorem wide_hl (k : Nat) (s : RegState) (ra rb lo hi : Nat)
    (hra : ra < 10) (hrb : rb < 10) (hlo : lo < 10) (hhi : hi < 10)
    (hlohi : lo ≠ hi) (hs : ∀ j, s j < M) :
    srun k s (wide ra rb lo hi) lo = (MulWide.hl (s ra) (s rb)).1 ∧
      srun k s (wide ra rb lo hi) hi = (MulWide.hl (s ra) (s rb)).2 := by
  apply Section413G1Denote.mulWideG_hl
  all_goals
    simp_all [Section413G1Denote.Distinct8, Section413G1Denote.NotIn8,
      s0, s1, s2, s3, s4, s5, s6, s7] <;> omega

private theorem wide_frame (k : Nat) (s : RegState)
    (ra rb lo hi j : Nat) (hjlo : j ≠ lo) (hjhi : j ≠ hi) (hj : j < 10) :
    srun k s (wide ra rb lo hi) j = s j := by
  apply Section413G1Denote.mulWideG_frame
  all_goals
    simp_all [Section413G1Denote.NotIn8,
      s0, s1, s2, s3, s4, s5, s6, s7] <;> omega

theorem prefix_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    let out := srun k s mulPrefix
    (out rLo, out rMid0) = MulWide.hl (s rXLo) (s rY) ∧
      (out rMid1, out rTop0) = MulWide.hl (s rXHi) (s rY) := by
  let t := srun k s (wide rXLo rY rLo rMid0)
  let out := srun k t (wide rXHi rY rMid1 rTop0)
  have h0 := wide_hl k s rXLo rY rLo rMid0
    (by decide) (by decide) (by decide) (by decide) (by decide) hs
  have htXHi : t rXHi = s rXHi :=
    wide_frame k s rXLo rY rLo rMid0 rXHi
      (by decide) (by decide) (by decide)
  have htY : t rY = s rY :=
    wide_frame k s rXLo rY rLo rMid0 rY
      (by decide) (by decide) (by decide)
  have htword : ∀ j, t j < M := srun_lt_of_lt k _ _ hs
  have h1 := wide_hl k t rXHi rY rMid1 rTop0
    (by decide) (by decide) (by decide) (by decide) (by decide) htword
  have houtLo : out rLo = t rLo :=
    wide_frame k t rXHi rY rMid1 rTop0 rLo
      (by decide) (by decide) (by decide)
  have houtMid0 : out rMid0 = t rMid0 :=
    wide_frame k t rXHi rY rMid1 rTop0 rMid0
      (by decide) (by decide) (by decide)
  simp only [mulPrefix, srun_append]
  change (out rLo, out rMid0) = _ ∧ (out rMid1, out rTop0) = _
  change t rLo = _ ∧ t rMid0 = _ at h0
  change out rMid1 = _ ∧ out rTop0 = _ at h1
  exact ⟨Prod.ext (houtLo.trans h0.1) (houtMid0.trans h0.2),
    Prod.ext (h1.1.trans (by rw [htXHi, htY]))
      (h1.2.trans (by rw [htXHi, htY]))⟩

private theorem combine_spec (k : Nat) (s : RegState)
    (htop : s rTop0 + 1 < M) :
    let out := srun k s combine
    out rLo = s rLo ∧
      out rMid = (s rMid0 + s rMid1) % M ∧
      out rTop = s rTop0 +
        (if (s rMid0 + s rMid1) % M < s rMid0 then 1 else 0) := by
  dsimp only
  have hc :
      (if (s rMid0 + s rMid1) % M < s rMid0 then 1 else 0) ≤ 1 := by
    split <;> omega
  simp only [combine, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rLo, rMid, rMid0, rMid1,
    rCarry, rTop, rTop0, M, Nat.reduceEqDiff, if_true, if_false]
  refine ⟨trivial, trivial, Nat.mod_eq_of_lt ?_⟩
  simp only [rTop0, M] at htop
  split <;> omega

/-- The literal register block returns all three exact product limbs. -/
theorem bodyG_spec (k : Nat) (s : RegState) (hs : ∀ j, s j < M) :
    let out := srun k s bodyG
    (out rLo, out rMid, out rTop) =
      MulWide3.mulWideByWord (s rXLo, s rXHi) (s rY) := by
  let t := srun k s mulPrefix
  have hp := prefix_spec k s hs
  change (t rLo, t rMid0) = MulWide.hl (s rXLo) (s rY) ∧
    (t rMid1, t rTop0) = MulWide.hl (s rXHi) (s rY) at hp
  have htword : ∀ j, t j < M := srun_lt_of_lt k _ _ hs
  have htopRoom : t rTop0 + 1 < M := by
    rw [show t rTop0 = (MulWide.hl (s rXHi) (s rY)).2 from
      congrArg Prod.snd hp.2]
    exact MulWide3.hl_hi_succ_lt _ _ (by simpa [M, MulWide.B64] using hs rXHi)
      (by simpa [M, MulWide.B64] using hs rY)
  have hc := combine_spec k t htopRoom
  have hp0lo : t rLo = (MulWide.hl (s rXLo) (s rY)).1 := by
    simpa using congrArg Prod.fst hp.1
  have hp0hi : t rMid0 = (MulWide.hl (s rXLo) (s rY)).2 := by
    simpa using congrArg Prod.snd hp.1
  have hp1lo : t rMid1 = (MulWide.hl (s rXHi) (s rY)).1 := by
    simpa using congrArg Prod.fst hp.2
  have hp1hi : t rTop0 = (MulWide.hl (s rXHi) (s rY)).2 := by
    simpa using congrArg Prod.snd hp.2
  simp only [bodyG, srun_append]
  change (srun k t combine rLo, srun k t combine rMid,
    srun k t combine rTop) = _
  rw [hc.1, hc.2.1, hc.2.2]
  simp only [MulWide3.mulWideByWord]
  rw [hp0lo, hp0hi, hp1lo, hp1hi]
  rfl

theorem body_arun_spec (k : Nat) (s : AState) (hs : ∀ j, s.regs j < M) :
    let out := arun k s body
    (out.regs rLo, out.regs rMid, out.regs rTop) =
        MulWide3.mulWideByWord (s.regs rXLo, s.regs rXHi) (s.regs rY) ∧
      out.arr = s.arr := by
  rw [body, arun_lift]
  exact ⟨bodyG_spec k s.regs hs, rfl⟩

end LeanCompCert.Ports.MulWide3Port

import LeanCompCert.Ports.RS62Loop314ProductSound
import LeanCompCert.Verified.ArrayRegFrame

/-! Soundness of the scale/compare/copy head of the RS62 (3.14) guard. -/

namespace LeanCompCert.Ports.RS62Loop314HeadSound

set_option maxRecDepth 3000000

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.RS62Loop314Program

private theorem frame (k r : Nat) (l : List AInstr) (s : AState)
    (h : ArrayRegFrame.writes r l = false) :
    (arun k s l).regs r = s.regs r :=
  ArrayRegFrame.arun_frame k r l h s

/-- Keep literal normalization abstract: instantiating this theorem does not
ask the kernel to reduce a large concrete multiplication under `% M`. -/
private theorem srun_mulLit_mod (k dst src L : Nat) (s : RegState)
    (hL : L < M) :
    (srun k s [.binop dst .mul (.reg src) (.lit L)]) dst = s src * L % M := by
  show (if dst = dst then (s src * (L % M)) % M else s dst) = _
  rw [if_pos rfl, Nat.mod_eq_of_lt hL]

/-- The analogous abstract one-instruction rule for unsigned division. -/
private theorem srun_udivLit_mod (k dst src L : Nat) (s : RegState)
    (hL : L < M) (h0 : L ≠ 0) :
    (srun k s [.binop dst .udiv (.reg src) (.lit L)]) dst =
      (s src / L) % M := by
  simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    Nat.mod_eq_of_lt hL, h0]

private theorem guardScaleLoBody_spec (k : Nat) (s : AState) :
    let out := arun k s guardScaleLoBody
    out.regs rNDLo = s.regs rN * RS62.fpD % M ∧ out.arr = s.arr := by
  rw [guardScaleLoBody, arun_lift]
  constructor
  · exact srun_mulLit_mod k rNDLo rN RS62.fpD s.regs (by decide)
  · rfl

private theorem guardScaleHiBody_spec (k : Nat) (s : AState)
    (hn : s.regs rN ≤ 2 ^ 40) :
    let out := arun k s guardScaleHiBody
    out.regs rNDHi = s.regs rN / 65536 ∧ out.arr = s.arr := by
  have hhi : s.regs rN / 65536 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (Nat.lt_of_le_of_lt hn (by decide))
  have hhiMod : s.regs rN / 65536 % M = s.regs rN / 65536 :=
    Nat.mod_eq_of_lt hhi
  simp only [rN, RS62PrimeMaskLadder.rN, M] at hhi hhiMod
  rw [guardScaleHiBody, arun_lift]
  constructor
  · calc
      _ = (s.regs rN / 65536) % M :=
        srun_udivLit_mod k rNDHi rN 65536 s.regs (by decide) (by decide)
      _ = s.regs rN / 65536 := hhiMod
  · rfl

private theorem guardScaleBody_spec (k : Nat) (s : AState)
    (hn : s.regs rN ≤ 2 ^ 40) :
    let out := arun k s guardScaleBody
    out.regs rNDLo = s.regs rN * RS62.fpD % M ∧
      out.regs rNDHi = s.regs rN / 65536 ∧ out.arr = s.arr := by
  let a := arun k s guardScaleLoBody
  let out := arun k a guardScaleHiBody
  have hlo := guardScaleLoBody_spec k s
  change a.regs rNDLo = s.regs rN * RS62.fpD % M ∧ a.arr = s.arr at hlo
  have hn' : a.regs rN ≤ 2 ^ 40 := by
    rw [frame k rN guardScaleLoBody s (by decide)]
    exact hn
  have hhi := guardScaleHiBody_spec k a hn'
  change out.regs rNDHi = a.regs rN / 65536 ∧ out.arr = a.arr at hhi
  have hout : arun k s guardScaleBody = out := by
    rw [guardScaleBody, arun_append]
  dsimp only
  rw [hout]
  refine ⟨?_, ?_, hhi.2.trans hlo.2⟩
  · rw [frame k rNDLo guardScaleHiBody a (by decide), hlo.1]
  · rw [hhi.1, frame k rN guardScaleLoBody s (by decide)]

private theorem guardDirectBody_spec (k : Nat) (s : AState) :
    let out := arun k s guardDirectBody
    out.regs rDone =
      (if s.regs rNDHi < s.regs rAccHi ∨
          s.regs rNDHi = s.regs rAccHi ∧ s.regs rNDLo ≤ s.regs rAccLo
        then 1 else 0) ∧ out.arr = s.arr := by
  rw [guardDirectBody, arun_lift]
  by_cases hh : s.regs rNDHi < s.regs rAccHi <;>
    by_cases he : s.regs rNDHi = s.regs rAccHi <;>
    by_cases hl : s.regs rNDLo ≤ s.regs rAccLo <;>
    simp only [rNDLo, rNDHi, rAccLo, rAccHi] at hh he hl <;>
    simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rNDLo, rNDHi, rHiLt, rHiEq, rLoLe, rEqLoLe, rDone,
      rAccLo, rAccHi, M, hh, he, hl]

private theorem guardDeltaCopyBody_spec (k : Nat) (s : AState) :
    let out := arun k s guardDeltaCopyBody
    out.regs rDeltaLo = s.regs rNDLo ∧
      out.regs rDeltaHi = s.regs rNDHi ∧
      out.regs rDone = s.regs rDone ∧ out.arr = s.arr := by
  rw [guardDeltaCopyBody, arun_lift]
  simp [srun, sdest, sval, denoteOperand, RegState.set,
    rDeltaLo, rDeltaHi, rNDLo, rNDHi, rDone]

/-- The head island forms the exact limbs of `n*2^48` and its direct
comparison with the accumulator. -/
theorem guardHeadBody_spec (k : Nat) (s : AState)
    (hn : s.regs rN ≤ 2 ^ 40)
    (_hAccLo : s.regs rAccLo < M) (_hAccHi : s.regs rAccHi < M) :
    let out := arun k s guardHeadBody
    out.regs rNDLo = s.regs rN * RS62.fpD % M ∧
      out.regs rNDHi = s.regs rN / 65536 ∧
      out.regs rDone =
        (if s.regs rN / 65536 < s.regs rAccHi ∨
            s.regs rN / 65536 = s.regs rAccHi ∧
              s.regs rN * RS62.fpD % M ≤ s.regs rAccLo
          then 1 else 0) ∧
      out.regs rDeltaLo = s.regs rN * RS62.fpD % M ∧
      out.regs rDeltaHi = s.regs rN / 65536 ∧ out.arr = s.arr := by
  let a := arun k s guardScaleBody
  let b := arun k a guardDirectBody
  let out := arun k b guardDeltaCopyBody
  have ha := guardScaleBody_spec k s hn
  change a.regs rNDLo = s.regs rN * RS62.fpD % M ∧
    a.regs rNDHi = s.regs rN / 65536 ∧ a.arr = s.arr at ha
  have hb := guardDirectBody_spec k a
  change b.regs rDone =
    (if a.regs rNDHi < a.regs rAccHi ∨
        a.regs rNDHi = a.regs rAccHi ∧ a.regs rNDLo ≤ a.regs rAccLo
      then 1 else 0) ∧ b.arr = a.arr at hb
  have hc := guardDeltaCopyBody_spec k b
  change out.regs rDeltaLo = b.regs rNDLo ∧
    out.regs rDeltaHi = b.regs rNDHi ∧
    out.regs rDone = b.regs rDone ∧ out.arr = b.arr at hc
  have haAccLo : a.regs rAccLo = s.regs rAccLo :=
    frame k rAccLo guardScaleBody s (by decide)
  have haAccHi : a.regs rAccHi = s.regs rAccHi :=
    frame k rAccHi guardScaleBody s (by decide)
  have hbNDLo : b.regs rNDLo = a.regs rNDLo :=
    frame k rNDLo guardDirectBody a (by decide)
  have hbNDHi : b.regs rNDHi = a.regs rNDHi :=
    frame k rNDHi guardDirectBody a (by decide)
  have hout : arun k s guardHeadBody = out := by
    rw [guardHeadBody, arun_append, arun_append]
  dsimp only
  rw [hout]
  refine ⟨?_, ?_, ?_, ?_, ?_, hc.2.2.2.trans (hb.2.trans ha.2.2)⟩
  · rw [frame k rNDLo guardDeltaCopyBody b (by decide), hbNDLo, ha.1]
  · rw [frame k rNDHi guardDeltaCopyBody b (by decide), hbNDHi, ha.2.1]
  · rw [hc.2.2.1, hb.1, ha.1, ha.2.1, haAccLo, haAccHi]
  · rw [hc.1, hbNDLo, ha.1]
  · rw [hc.2.1, hbNDHi, ha.2.1]

end LeanCompCert.Ports.RS62Loop314HeadSound

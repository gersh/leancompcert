import LeanCompCert.Ports.R2SegLogRoundFold
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.BlockDefined

/-!
# Reset/preserve island before the `R₂*` fixed-log round

The seven scalar instructions immediately before the relocated round either
install `n << (62-e)` and clear the bit accumulator (first round), or preserve
the previous mantissa and accumulator (continuation round).  These exact
semantics connect the finite round telescope to the production entry gate.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

def logRoundInitInstrs : List Instr :=
  [ .binop 219 .sub (.lit 62) (.reg rEx)
  , .binop 220 .band (.reg 219) (.lit 63)
  , .binop 221 .shl (.reg rNe) (.reg 220)
  , .binop 222 .mul (.reg 208) (.reg 221)
  , .binop 223 .mul (.reg 209) (.reg rXm)
  , .binop rXm .add (.reg 222) (.reg 223)
  , .binop rAa .mul (.reg rAa) (.reg 209) ]

def logRoundInitBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift logRoundInitInstrs

theorem logRoundInitBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 25).take 7 = logRoundInitBody := by
  rfl

/-- At the first round, the entry gate installs the normalized mantissa and
clears the accumulated fractional bits. -/
theorem logRoundInitInstrs_start_run (k : Nat) (s : RegState)
    (n e : Nat) (h208 : s 208 = 1) (h209 : s 209 = 0)
    (hne : s rNe = n) (he : s rEx = e) (he62 : e ≤ 62)
    (hnorm : n <<< (62 - e) < M) :
    let out := srun k s logRoundInitInstrs
    out rXm = n <<< (62 - e) ∧ out rAa = 0 := by
  have hsub : (62 + (M - e)) % M = 62 - e := by
    have hs := LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (a := 62) (b := e) he62 (by decide)
    exact Option.some.inj hs
  have hmask : (63 : Nat) % M = 63 := by decide
  have hshift : (62 - e) &&& 63 = 62 - e := by
    have hlt : 62 - e < 64 := by omega
    change (62 - e) &&& (2 ^ 6 - 1) = 62 - e
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  have hshiftM : 62 - e < M :=
    Nat.lt_trans (show 62 - e < 64 by omega) (by decide)
  have hne' : s 194 = n := by simpa only [rNe] using hne
  have he' : s 186 = e := by simpa only [rEx] using he
  simp [logRoundInitInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h208, h209, hne', he', hsub, hmask, hshift,
    Nat.mod_eq_of_lt hshiftM, Nat.mod_eq_of_lt hnorm,
    rNe, rEx, rXm, rAa]

/-- On a continuation round, the same island preserves both recurrence
registers. -/
theorem logRoundInitInstrs_continue_run (k : Nat) (s : RegState)
    (n e x a : Nat) (h208 : s 208 = 0) (h209 : s 209 = 1)
    (hne : s rNe = n) (he : s rEx = e) (hx : s rXm = x)
    (ha : s rAa = a) (he62 : e ≤ 62)
    (hnorm : n <<< (62 - e) < M) (hxM : x < M) (haM : a < M) :
    let out := srun k s logRoundInitInstrs
    out rXm = x ∧ out rAa = a := by
  have hsub : (62 + (M - e)) % M = 62 - e := by
    have hs := LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (a := 62) (b := e) he62 (by decide)
    exact Option.some.inj hs
  have hmask : (63 : Nat) % M = 63 := by decide
  have hshift : (62 - e) &&& 63 = 62 - e := by
    have hlt : 62 - e < 64 := by omega
    change (62 - e) &&& (2 ^ 6 - 1) = 62 - e
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  have hshiftM : 62 - e < M :=
    Nat.lt_trans (show 62 - e < 64 by omega) (by decide)
  have hne' : s 194 = n := by simpa only [rNe] using hne
  have he' : s 186 = e := by simpa only [rEx] using he
  have hx' : s 196 = x := by simpa only [rXm] using hx
  have ha' : s 197 = a := by simpa only [rAa] using ha
  simp [logRoundInitInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h208, h209, hne', he', hx', ha', hsub, hmask,
    hshift, Nat.mod_eq_of_lt hshiftM, Nat.mod_eq_of_lt hnorm,
    Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt haM,
    rNe, rEx, rXm, rAa]

theorem logRoundInitBody_start_run (k : Nat) (s : AState)
    (n e : Nat) (h208 : s.regs 208 = 1) (h209 : s.regs 209 = 0)
    (hne : s.regs rNe = n) (he : s.regs rEx = e) (he62 : e ≤ 62)
    (hnorm : n <<< (62 - e) < M) :
    let out := arun k s logRoundInitBody
    out.regs rXm = n <<< (62 - e) ∧ out.regs rAa = 0 ∧
      out.arr = s.arr := by
  rw [logRoundInitBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logRoundInitInstrs_start_run k s.regs n e
    h208 h209 hne he he62 hnorm
  exact ⟨h.1, h.2, rfl⟩

theorem logRoundInitBody_continue_run (k : Nat) (s : AState)
    (n e x a : Nat) (h208 : s.regs 208 = 0) (h209 : s.regs 209 = 1)
    (hne : s.regs rNe = n) (he : s.regs rEx = e)
    (hx : s.regs rXm = x) (ha : s.regs rAa = a) (he62 : e ≤ 62)
    (hnorm : n <<< (62 - e) < M) (hxM : x < M) (haM : a < M) :
    let out := arun k s logRoundInitBody
    out.regs rXm = x ∧ out.regs rAa = a ∧ out.arr = s.arr := by
  rw [logRoundInitBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := logRoundInitInstrs_continue_run k s.regs n e x a
    h208 h209 hne he hx ha he62 hnorm hxM haM
  exact ⟨h.1, h.2, rfl⟩

#print axioms logRoundInitBody_eq_slice
#print axioms logRoundInitInstrs_start_run
#print axioms logRoundInitInstrs_continue_run
#print axioms logRoundInitBody_start_run
#print axioms logRoundInitBody_continue_run

end LeanCompCert.Ports.R2SegSieve

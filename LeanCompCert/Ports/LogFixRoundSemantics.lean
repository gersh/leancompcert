import LeanCompCert.Ports.LogFixPort
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.RegFrame

/-!
# Exact semantics of one compiled fixed-logarithm round

The compiler bridge for `LogFixPort` already proves that the emitted program
implements its instruction denotation.  This module identifies that literal
20-instruction denotation with the `LogFixed.logMant`/`logBit` recurrence,
using small arithmetic stages so elaboration never expands the whole register
state tower at once.
-/

namespace LeanCompCert.Ports.LogFixPort

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.LogFixed

def splitInstrs : List Instr := logRoundBody.take 2
def productInstrs : List Instr := (logRoundBody.drop 2).take 3
def partInstrs : List Instr := (logRoundBody.drop 5).take 4
def carryInstrs : List Instr := (logRoundBody.drop 9).take 3
def combineInstrs : List Instr := (logRoundBody.drop 12).take 4
def emitInstrs : List Instr := logRoundBody.drop 16

theorem logRoundBody_eq_stages :
    logRoundBody = splitInstrs ++ productInstrs ++ partInstrs ++
      carryInstrs ++ combineInstrs ++ emitInstrs := by
  rfl

private theorem splitInstrs_run (k : Nat) (s : RegState) (x : Nat)
    (hx : s rX = x) (hxM : x < M) :
    let out := srun k s splitInstrs
    out 2 = x / B32 ∧ out 3 = x % B32 := by
  have h32 : (32 : Nat) % M = 32 := by decide
  have hmask : (4294967295 : Nat) % M = 4294967295 := by decide
  have hdivM : x / B32 < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxM
  have hmodM : x % B32 < M :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hand : x &&& 4294967295 = x % B32 := by
    simpa only [B32] using Nat.and_two_pow_sub_one_eq_mod x 32
  have hx' : s 0 = x := by simpa only [rX] using hx
  simp only [B32] at hdivM hmodM hand ⊢
  simp [splitInstrs, logRoundBody, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, rX, hx', h32, hmask, hand,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hdivM,
    Nat.mod_eq_of_lt hmodM]

private theorem productInstrs_run (k : Nat) (s : RegState) (x1 x0 : Nat)
    (h2 : s 2 = x1) (h3 : s 3 = x0)
    (hhi : x1 * x1 < M) (hmid : x1 * x0 < M)
    (hlo : x0 * x0 < M) :
    let out := srun k s productInstrs
    out 4 = x1 * x1 ∧ out 5 = x1 * x0 ∧ out 6 = x0 * x0 := by
  simp [productInstrs, logRoundBody, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h2, h3, Nat.mod_eq_of_lt hhi,
    Nat.mod_eq_of_lt hmid, Nat.mod_eq_of_lt hlo]

private theorem partInstrs_run (k : Nat) (s : RegState) (mid lo : Nat)
    (h5 : s 5 = mid) (h6 : s 6 = lo)
    (hmidM : mid < M) (hloM : lo < M) :
    let out := srun k s partInstrs
    out 7 = mid / B29 ∧ out 8 = mid % B29 ∧
      out 9 = lo / B62 ∧ out 10 = lo % B62 := by
  have h29 : (29 : Nat) % M = 29 := by decide
  have h62 : (62 : Nat) % M = 62 := by decide
  have hm29 : (536870911 : Nat) % M = 536870911 := by decide
  have hm62 : (4611686018427387903 : Nat) % M =
      4611686018427387903 := by decide
  have hmidDiv : mid / B29 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hmidM
  have hloDiv : lo / B62 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hloM
  have hmidMod : mid % B29 < M :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hloMod : lo % B62 < M :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hand29 : mid &&& 536870911 = mid % B29 := by
    simpa only [B29] using Nat.and_two_pow_sub_one_eq_mod mid 29
  have hand62 : lo &&& 4611686018427387903 = lo % B62 := by
    simpa only [B62] using Nat.and_two_pow_sub_one_eq_mod lo 62
  simp only [B29] at hmidDiv hmidMod hand29 ⊢
  simp only [B62] at hloDiv hloMod hand62 ⊢
  simp [partInstrs, logRoundBody, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h5, h6, h29, h62, hm29, hm62,
    hand29, hand62, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hmidDiv, Nat.mod_eq_of_lt hloDiv,
    Nat.mod_eq_of_lt hmidMod, Nat.mod_eq_of_lt hloMod]

private theorem carryInstrs_run (k : Nat) (s : RegState) (ml cl : Nat)
    (h8 : s 8 = ml) (h10 : s 10 = cl)
    (hshift : ml <<< 33 < M) (hsum : (ml <<< 33) + cl < M) :
    let out := srun k s carryInstrs
    out 12 = (ml <<< 33) + cl ∧
      out 13 = if B62 ≤ (ml <<< 33) + cl then 1 else 0 := by
  have h33 : (33 : Nat) % M = 33 := by decide
  have hB62 : (4611686018427387904 : Nat) % M =
      4611686018427387904 := by decide
  simp [carryInstrs, logRoundBody, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h8, h10, h33, hB62,
    Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hsum, B62]

private theorem combineInstrs_run (k : Nat) (s : RegState)
    (hi mh ch carry : Nat)
    (h4 : s 4 = hi) (h7 : s 7 = mh) (h9 : s 9 = ch)
    (h13 : s 13 = carry)
    (h4hi : hi <<< 2 < M) (h15 : (hi <<< 2) + mh < M)
    (h16 : (hi <<< 2) + mh + ch < M)
    (hy : (hi <<< 2) + mh + ch + carry < M) :
    (srun k s combineInstrs) 17 = (hi <<< 2) + mh + ch + carry := by
  have h2 : (2 : Nat) % M = 2 := by decide
  simp [combineInstrs, logRoundBody, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, h4, h7, h9, h13, h2,
    Nat.mod_eq_of_lt h4hi, Nat.mod_eq_of_lt h15,
    Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt hy]

private theorem emitInstrs_run (k : Nat) (s : RegState) (y a bit : Nat)
    (h17 : s 17 = y) (ha : s rA = a)
    (hbit : bit = if B63 ≤ y then 1 else 0)
    (hyM : y < M) (hrenorm : y >>> bit < M)
    (ha2 : a <<< 1 < M) (hout : (a <<< 1) + bit < M) :
    let out := srun k s emitInstrs
    out rX = y >>> bit ∧ out rA = (a <<< 1) + bit := by
  have hB63 : (9223372036854775808 : Nat) % M =
      9223372036854775808 := by decide
  have h1 : (1 : Nat) % M = 1 := by decide
  have ha' : s 1 = a := by simpa only [rA] using ha
  subst bit
  by_cases hb : B63 ≤ y
  · have hbN : (9223372036854775808 : Nat) ≤ y := by
      simpa only [B63] using hb
    have hrenorm1 : y >>> 1 < M := by simpa only [hb, if_true] using hrenorm
    have hout1 : (a <<< 1) + 1 < M := by simpa only [hb, if_true] using hout
    simp [emitInstrs, logRoundBody, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, rX, rA, h17, ha', hB63, h1, B63, hbN,
      Nat.mod_eq_of_lt hrenorm1, Nat.mod_eq_of_lt ha2,
      Nat.mod_eq_of_lt hout1]
  · have hbN : ¬(9223372036854775808 : Nat) ≤ y := by
      simpa only [B63] using hb
    simp [emitInstrs, logRoundBody, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, rX, rA, h17, ha', hB63, h1, B63, hbN,
      Nat.mod_eq_of_lt hyM, Nat.mod_eq_of_lt ha2]

/-- Staged exact semantics.  The hypotheses are precisely the word-headroom
facts needed to remove the machine's modulo reductions. -/
theorem logRoundBody_srun (k : Nat) (s : RegState) (x a : Nat)
    (hx : s rX = x) (ha : s rA = a) (hxM : x < M)
    (hhi : (x / B32) * (x / B32) < M)
    (hmid : (x / B32) * (x % B32) < M)
    (hlo : (x % B32) * (x % B32) < M)
    (hshift : (((x / B32) * (x % B32)) % B29) <<< 33 < M)
    (hcarrySum : ((((x / B32) * (x % B32)) % B29) <<< 33) +
      ((x % B32) * (x % B32)) % B62 < M)
    (h4hi : ((x / B32) * (x / B32)) <<< 2 < M)
    (h15 : (((x / B32) * (x / B32)) <<< 2) +
      ((x / B32) * (x % B32)) / B29 < M)
    (h16 : (((x / B32) * (x / B32)) <<< 2) +
      ((x / B32) * (x % B32)) / B29 +
      ((x % B32) * (x % B32)) / B62 < M)
    (hy : sq62 x < M) (hrenorm : logMant x < M)
    (ha2 : a <<< 1 < M)
    (hout : (a <<< 1) + logBit x < M) :
    let out := srun k s logRoundBody
    out rX = logMant x ∧ out rA = (a <<< 1) + logBit x := by
  let x1 := x / B32
  let x0 := x % B32
  let hi := x1 * x1
  let mid := x1 * x0
  let lo := x0 * x0
  let mh := mid / B29
  let ml := mid % B29
  let ch := lo / B62
  let cl := lo % B62
  let carry := if B62 ≤ (ml <<< 33) + cl then 1 else 0
  let y := (hi <<< 2) + mh + ch + carry
  let bit := if B63 ≤ y then 1 else 0
  let s1 := srun k s splitInstrs
  let s2 := srun k s1 productInstrs
  let s3 := srun k s2 partInstrs
  let s4 := srun k s3 carryInstrs
  let s5 := srun k s4 combineInstrs
  have hs1 := splitInstrs_run k s x hx hxM
  have hs2 := productInstrs_run k s1 x1 x0 hs1.1 hs1.2 hhi hmid hlo
  have hs3 := partInstrs_run k s2 mid lo hs2.2.1 hs2.2.2 hmid hlo
  have hs4 := carryInstrs_run k s3 ml cl hs3.2.1 hs3.2.2.2 hshift hcarrySum
  have hyEq : y = sq62 x := by
    simp only [y, hi, mh, ch, carry, ml, cl, mid, lo, x1, x0,
      sq62, Nat.shiftLeft_eq]
    rw [show (2 : Nat) ^ 2 = 4 by decide,
      show (2 : Nat) ^ 33 = 8589934592 by decide]
    rw [Nat.mul_comm ((x / B32) * (x / B32)) 4]
  have hy' : y < M := by rw [hyEq]; exact hy
  have hs5 := combineInstrs_run k s4 hi mh ch carry
    hs2.1 hs3.1 hs3.2.2.1 hs4.2 h4hi h15 h16 hy'
  have hbitEq : bit = logBit x := by simp only [bit, logBit, hyEq]
  have hrenorm' : y >>> bit < M := by
    rw [hbitEq, hyEq]
    exact hrenorm
  have hs6 := emitInstrs_run k s5 y a bit hs5
    ((LeanCompCert.Verified.RegFrame.srun_frame k rA combineInstrs
      (by rfl) s4).trans
      ((LeanCompCert.Verified.RegFrame.srun_frame k rA carryInstrs
        (by rfl) s3).trans
        ((LeanCompCert.Verified.RegFrame.srun_frame k rA partInstrs
          (by rfl) s2).trans
          ((LeanCompCert.Verified.RegFrame.srun_frame k rA productInstrs
            (by rfl) s1).trans
            ((LeanCompCert.Verified.RegFrame.srun_frame k rA splitInstrs
              (by rfl) s).trans ha)))))
    rfl hy' hrenorm'
    ha2 (by simpa only [hbitEq] using hout)
  rw [logRoundBody_eq_stages, srun_append, srun_append, srun_append,
    srun_append, srun_append]
  exact ⟨hs6.1.trans (by simp only [logMant, hbitEq, hyEq]),
    hs6.2.trans (by rw [hbitEq])⟩

private theorem sq62_eq_shift_parts (x : Nat) :
    sq62 x =
      (((x / B32) * (x / B32)) <<< 2) +
        ((x / B32) * (x % B32)) / B29 +
        ((x % B32) * (x % B32)) / B62 +
        (if B62 ≤
          ((((x / B32) * (x % B32)) % B29) <<< 33) +
            ((x % B32) * (x % B32)) % B62 then 1 else 0) := by
  simp only [sq62, Nat.shiftLeft_eq]
  rw [show (2 : Nat) ^ 2 = 4 by decide,
    show (2 : Nat) ^ 33 = 8589934592 by decide]
  rw [Nat.mul_comm ((x / B32) * (x / B32)) 4]

/-- A normalized mantissa and an accumulator below `2^62` automatically
satisfy every word-headroom premise of `logRoundBody_srun`. -/
theorem logRoundBody_srun_of_range (k : Nat) (s : RegState) (x a : Nat)
    (hx : s rX = x) (ha : s rA = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := srun k s logRoundBody
    out rX = logMant x ∧ out rA = (a <<< 1) + logBit x := by
  have hxM : x < M := Nat.lt_trans hxhi (by decide)
  have hx1 : x / B32 < 2 ^ 31 := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < B32)).2
    calc
      x < B63 := hxhi
      _ = (2 ^ 31) * B32 := by decide
  have hx0 : x % B32 < B32 := Nat.mod_lt _ (by decide)
  have hhi62 : (x / B32) * (x / B32) < B62 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt hx1 hx1
    simpa only [B62, show (2 : Nat) ^ 31 * 2 ^ 31 = 2 ^ 62 by decide]
      using h
  have hhi : (x / B32) * (x / B32) < M :=
    Nat.lt_trans hhi62 (by decide)
  have hmid63 : (x / B32) * (x % B32) < B63 := by
    have h := Nat.mul_lt_mul_of_lt_of_lt hx1 hx0
    simpa only [B32, B63,
      show (2 : Nat) ^ 31 * 2 ^ 32 = 2 ^ 63 by decide] using h
  have hmid : (x / B32) * (x % B32) < M :=
    Nat.lt_trans hmid63 (by decide)
  have hlo : (x % B32) * (x % B32) < M := by
    have h := LeanCompCert.Verified.MulWide.mul_lt_mul_of_lt_of_lt hx0 hx0
    simpa only [B32, M,
      show (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 by decide] using h
  have hml : ((x / B32) * (x % B32)) % B29 < B29 :=
    Nat.mod_lt _ (by decide)
  have hshift62 :
      (((x / B32) * (x % B32)) % B29) <<< 33 < B62 := by
    simp only [Nat.shiftLeft_eq]
    have h := (Nat.mul_lt_mul_right (Nat.pow_pos (by decide) : 0 < 2 ^ 33)).2 hml
    simpa only [B29, B62,
      show (2 : Nat) ^ 29 * 2 ^ 33 = 2 ^ 62 by decide] using h
  have hshift :
      (((x / B32) * (x % B32)) % B29) <<< 33 < M :=
    Nat.lt_trans hshift62 (by decide)
  have hcl : ((x % B32) * (x % B32)) % B62 < B62 :=
    Nat.mod_lt _ (by decide)
  have hcarrySum :
      ((((x / B32) * (x % B32)) % B29) <<< 33) +
        ((x % B32) * (x % B32)) % B62 < M := by
    have hB : B62 + B62 ≤ M := by decide
    omega
  have h4hi : ((x / B32) * (x / B32)) <<< 2 < M := by
    simp only [Nat.shiftLeft_eq]
    have h := (Nat.mul_lt_mul_right (show 0 < (2 : Nat) ^ 2 by decide)).2 hhi62
    simpa only [B62, M,
      show (2 : Nat) ^ 62 * 2 ^ 2 = 2 ^ 64 by decide] using h
  have hxx : x * x < B63 * B63 :=
    Nat.mul_lt_mul_of_lt_of_lt hxhi hxhi
  have hy : sq62 x < M := by
    rw [sq62_eq]
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < B62)).2
    calc
      x * x < B63 * B63 := hxx
      _ = M * B62 := by decide
  have hform := sq62_eq_shift_parts x
  have h15 : (((x / B32) * (x / B32)) <<< 2) +
      ((x / B32) * (x % B32)) / B29 < M := by
    apply Nat.lt_of_le_of_lt _ hy
    rw [hform]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have h16 : (((x / B32) * (x / B32)) <<< 2) +
      ((x / B32) * (x % B32)) / B29 +
      ((x % B32) * (x % B32)) / B62 < M := by
    apply Nat.lt_of_le_of_lt _ hy
    rw [hform]
    exact Nat.le_add_right _ _
  have hmRange := logMant_range hxlo hxhi
  have hrenorm : logMant x < M := Nat.lt_trans hmRange.2 (by decide)
  have ha2B63 : a <<< 1 < B63 := by
    simp only [Nat.shiftLeft_eq]
    have h := (Nat.mul_lt_mul_right (show 0 < (2 : Nat) ^ 1 by decide)).2 haBound
    simpa only [B62, B63,
      show (2 : Nat) ^ 62 * 2 ^ 1 = 2 ^ 63 by decide] using h
  have ha2 : a <<< 1 < M := Nat.lt_trans ha2B63 (by decide)
  have hbit := logBit_le_one x
  have hout : (a <<< 1) + logBit x < M := by
    have hB : B63 + 1 ≤ M := by decide
    omega
  exact logRoundBody_srun k s x a hx ha hxM hhi hmid hlo hshift
    hcarrySum h4hi h15 h16 hy hrenorm ha2 hout

#print axioms logRoundBody_eq_stages
#print axioms logRoundBody_srun
#print axioms logRoundBody_srun_of_range

end LeanCompCert.Ports.LogFixPort

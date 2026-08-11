import LeanCompCert.Ports.R2SegSieve
import LeanCompCert.Verified.ArrayScalarBlock
import LeanCompCert.Verified.RegFrame

/-!
# Classification refinement for the `R₂*` segmented sieve

The marking phase of `R2SegSieve` leaves three physical planes.  This file
isolates the small scalar selector which turns those planes into one of the
four source coefficient modes.  Keeping the selector separate prevents a
proof about a few dozen scalar instructions from normalizing the complete
segmented program.

The remaining marking proof must establish the hypotheses supplied here:
the normalized product, saturated distinct-prime count, and first two fixed
logarithmic weights stored in the planes.  Once those facts are available,
the theorems below identify the actual emitted selector with the source
prime-power cases.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge (arun)
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift_regs)
open LeanCompCert.Verified.InstrBlock

/-- Logical inputs read from the three marking planes.  `large = true` means
that their small-prime product is not the candidate, so one prime factor
larger than the sieve root remains. -/
structure ClassInput where
  large : Bool
  count : Nat
  w1 : Nat
  w2 : Nat
  lsum : Nat
  deriving Repr, DecidableEq

/-- The semantic payload produced by the classifier before stream packing. -/
structure ClassResult where
  qualifies : Bool
  mode : Nat
  first : Nat
  aux : Nat
  deriving Repr, DecidableEq

/-- Pure form of the four selector modes in `R2Cfg.classBody`. -/
def classifyPlanes (x : ClassInput) : ClassResult :=
  if x.count = 0 ∧ x.large then
    ⟨true, 0, x.w1, x.lsum⟩
  else if x.count = 1 ∧ x.large then
    ⟨true, 1, x.w1, x.lsum⟩
  else if x.count = 1 ∧ !x.large then
    ⟨true, 2, x.w1, x.lsum⟩
  else if x.count = 2 ∧ !x.large then
    ⟨true, 3, x.w1, x.w2⟩
  else
    ⟨false, 4, x.w1, x.lsum⟩

@[simp] theorem classifyPlanes_mode0 (w1 w2 lsum : Nat) :
    classifyPlanes ⟨true, 0, w1, w2, lsum⟩ =
      ⟨true, 0, w1, lsum⟩ := by
  simp [classifyPlanes]

@[simp] theorem classifyPlanes_mode1 (w1 w2 lsum : Nat) :
    classifyPlanes ⟨true, 1, w1, w2, lsum⟩ =
      ⟨true, 1, w1, lsum⟩ := by
  simp [classifyPlanes]

@[simp] theorem classifyPlanes_mode2 (w1 w2 lsum : Nat) :
    classifyPlanes ⟨false, 1, w1, w2, lsum⟩ =
      ⟨true, 2, w1, lsum⟩ := by
  simp [classifyPlanes]

@[simp] theorem classifyPlanes_mode3 (w1 w2 lsum : Nat) :
    classifyPlanes ⟨false, 2, w1, w2, lsum⟩ =
      ⟨true, 3, w1, w2⟩ := by
  simp [classifyPlanes]

theorem classifyPlanes_none {x : ClassInput}
    (h : ¬(x.count = 0 ∧ x.large) ∧
      ¬(x.count = 1 ∧ x.large) ∧
      ¬(x.count = 1 ∧ !x.large) ∧
      ¬(x.count = 2 ∧ !x.large)) :
    classifyPlanes x = ⟨false, 4, x.w1, x.lsum⟩ := by
  rcases x with ⟨large, count, w1, w2, lsum⟩
  cases large <;> simp_all [classifyPlanes]

/-- Factors selected later by `R2Cfg.logBody`, after `lnN` has been computed.
The boolean records whether the jump is positive. -/
def ClassResult.jumpFactors (x : ClassResult) (lnN : Nat) : Bool × Nat × Nat :=
  match x.mode with
  | 0 => (false, lnN - x.aux, lnN - x.aux)
  | 1 => (true, x.first, lnN - x.aux)
  | 2 => (false, x.first, x.first)
  | 3 => (true, x.first, x.aux)
  | _ => (false, 0, 0)

@[simp] theorem mode0_jumpFactors (lnN : Nat) :
    (classifyPlanes ⟨true, 0, 0, 0, 0⟩).jumpFactors lnN =
      (false, lnN, lnN) := by
  simp [ClassResult.jumpFactors]

@[simp] theorem mode1_jumpFactors (w lsum lnN : Nat) :
    (classifyPlanes ⟨true, 1, w, 0, lsum⟩).jumpFactors lnN =
      (true, w, lnN - lsum) := by
  simp [ClassResult.jumpFactors]

@[simp] theorem mode2_jumpFactors (w lsum lnN : Nat) :
    (classifyPlanes ⟨false, 1, w, 0, lsum⟩).jumpFactors lnN =
      (false, w, w) := by
  simp [ClassResult.jumpFactors]

@[simp] theorem mode3_jumpFactors (w1 w2 lsum lnN : Nat) :
    (classifyPlanes ⟨false, 2, w1, w2, lsum⟩).jumpFactors lnN =
      (true, w1, w2) := by
  simp [ClassResult.jumpFactors]

/-- Exact scalar slice of `R2Cfg.classBody` which selects and packs a mode.
Its equality with the corresponding slice of the production body is proved
below, so this is not an independent reimplementation used only by a test. -/
def classFlagInstrs : List Instr :=
    [ .binop 105 .eq (.reg 96) (.lit 0)
    , .binop 106 .eq (.reg 96) (.lit 1)
    , .binop 107 .eq (.reg 96) (.lit 2)
    , .binop 108 .sub (.lit 1) (.reg 95)
    , .binop 109 .mul (.reg 105) (.reg 95)
    , .binop 110 .mul (.reg 106) (.reg 95)
    , .binop 111 .mul (.reg 106) (.reg 108)
    , .binop 112 .mul (.reg 107) (.reg 108)
    , .binop 113 .add (.reg 109) (.reg 110)
    , .binop 114 .add (.reg 111) (.reg 112)
    , .binop 115 .add (.reg 113) (.reg 114)
    , .binop 116 .mul (.reg 115) (.reg 9) ]

def classModeInstrs : List Instr :=
    [ .binop 117 .shl (.reg 111) (.lit 1)
    , .binop 118 .mul (.reg 112) (.lit 3)
    , .binop 119 .add (.reg 110) (.reg 117)
    , .binop 120 .add (.reg 119) (.reg 118) ]

def classPayloadInstrs : List Instr :=
    [ .binop 121 .mul (.reg 112) (.reg 99)
    , .binop 122 .sub (.lit 1) (.reg 112)
    , .binop 123 .mul (.reg 122) (.reg 91)
    , .binop 124 .add (.reg 121) (.reg 123)
    , .binop 125 .shl (.reg 124) (.lit wtBits)
    , .binop 126 .shl (.reg 120) (.lit 57)
    , .binop 127 .add (.reg 97) (.reg 125)
    , .binop 128 .add (.reg 127) (.reg 126) ]

def classSelectorInstrs : List Instr :=
  classFlagInstrs ++ classModeInstrs ++ classPayloadInstrs

def classSelectorBody : List AInstr := lift classSelectorInstrs

/-- Registers observed immediately after the selector. -/
def selectorResult (s : AState) : Nat × Nat × Nat × Nat :=
  (s.regs 115, s.regs 120, s.regs 116, s.regs 128)

/-- Arithmetic encoding of a pure classification result. -/
def ClassResult.machineResult (x : ClassResult) (active : Nat) :
    Nat × Nat × Nat × Nat :=
  let q := if x.qualifies then 1 else 0
  let m := if x.qualifies then x.mode else 0
  (q, m, q * active,
    x.first + (x.aux <<< wtBits) + (m <<< 57))

/-- The selector block is literally the corresponding production-body slice.
This guards against the helper silently drifting away from emitted code. -/
theorem classSelectorBody_eq_slice (c : R2Cfg) :
    (c.classBody.drop 23).take classSelectorBody.length = classSelectorBody := by
  rfl

def flagResult (s : RegState) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (s 110, s 111, s 112, s 115, s 116, s 108)

set_option maxRecDepth 10000

/-- The first selector stage computes the three live mode bits, their sum,
the gated push bit, and the complement of the large-factor bit. -/
theorem classFlagInstrs_run (k : Nat) (s : RegState) (x : ClassInput)
    (active : Nat)
    (hlarge : s 95 = if x.large then 1 else 0)
    (hcount : s 96 = x.count) (hactive : s 9 = active)
    (hcountBound : x.count ≤ 2) (hactiveBit : active ≤ 1) :
    let out := LeanCompCert.Verified.InstrBlock.srun k s classFlagInstrs
    let pure := classifyPlanes x
    flagResult out =
      (if pure.mode = 1 then 1 else 0,
       if pure.mode = 2 then 1 else 0,
       if pure.mode = 3 then 1 else 0,
       if pure.qualifies then 1 else 0,
       (if pure.qualifies then 1 else 0) * active,
       if x.large then 0 else 1) := by
  cases x with
  | mk large count w1 w2 lsum =>
      simp only at hlarge hcount hcountBound
      have hc : count = 0 ∨ count = 1 ∨ count = 2 := by omega
      rcases hc with rfl | rfl | rfl <;> cases large <;>
        simp_all [classFlagInstrs, flagResult, classifyPlanes,
          LeanCompCert.Verified.InstrBlock.srun, RegState.set,
          sdest, sval, denoteOperand, denoteOp, M,
          Nat.mod_eq_of_lt] <;> omega

/-- The second selector stage encodes the three mutually exclusive live mode
bits as `1`, `2`, or `3`; mode zero is already represented by all-zero bits. -/
theorem classModeInstrs_run (k : Nat) (s : RegState)
    (m1 m2 m3 : Nat)
    (h1 : s 110 = m1) (h2 : s 111 = m2) (h3 : s 112 = m3)
    (hm1 : m1 ≤ 1) (hm2 : m2 ≤ 1) (hm3 : m3 ≤ 1) :
    (LeanCompCert.Verified.InstrBlock.srun k s classModeInstrs) 120 =
      m1 + 2 * m2 + 3 * m3 := by
  simp [classModeInstrs, LeanCompCert.Verified.InstrBlock.srun,
    RegState.set, sdest, sval, denoteOperand, denoteOp, h1, h2, h3,
    M, Nat.mod_eq_of_lt]
  omega

private theorem payload_bounds (w1 aux mode : Nat)
    (hw1 : w1 < 2 ^ wtBits) (haux : aux < 2 ^ 29)
    (hmode : mode ≤ 3) :
    w1 < M ∧ aux < M ∧ mode < M ∧
      aux <<< wtBits < M ∧ mode <<< 57 < M ∧
      w1 + (aux <<< wtBits) < M ∧
      w1 + (aux <<< wtBits) + (mode <<< 57) < M := by
  simp only [wtBits, M, Nat.shiftLeft_eq] at *
  omega

/-- The final selector stage packs `w1`, the selected auxiliary weight, and
the two-bit mode into the stream payload. -/
theorem classPayloadInstrs_run (k : Nat) (s : RegState)
    (m3 mode w1 w2 lsum : Nat)
    (hm3 : s 112 = m3) (hmode : s 120 = mode)
    (hw1 : s 97 = w1) (hw2 : s 99 = w2) (hlsum : s 91 = lsum)
    (hm3Bit : m3 ≤ 1) (hmodeBound : mode ≤ 3)
    (hw1Bound : w1 < 2 ^ wtBits)
    (hw2Bound : w2 < 2 ^ wtBits)
    (hlsumBound : lsum < 2 ^ 29) :
    (LeanCompCert.Verified.InstrBlock.srun k s classPayloadInstrs) 128 =
      w1 + ((if m3 = 1 then w2 else lsum) <<< wtBits) + (mode <<< 57) := by
  have hm3Cases : m3 = 0 ∨ m3 = 1 := by omega
  have h28 : 28 % M = 28 := by decide +kernel
  have h57 : 57 % M = 57 := by decide +kernel
  have hzero : (1 + (M - 1)) % M = 0 := by decide +kernel
  rcases hm3Cases with rfl | rfl
  · have hb := payload_bounds w1 lsum mode hw1Bound hlsumBound hmodeBound
    have hlsumM : lsum % M = lsum := Nat.mod_eq_of_lt hb.2.1
    have hpackM :
        (w1 + (lsum <<< wtBits) + (mode <<< 57)) % M =
          w1 + (lsum <<< wtBits) + (mode <<< 57) :=
      Nat.mod_eq_of_lt hb.2.2.2.2.2.2
    have hpack28 :
        (w1 + (lsum <<< 28) + (mode <<< 57)) % M =
          w1 + (lsum <<< 28) + (mode <<< 57) := by
      simpa only [wtBits] using hpackM
    simp [classPayloadInstrs, LeanCompCert.Verified.InstrBlock.srun,
      RegState.set, sdest, sval, denoteOperand, denoteOp, hm3, hmode,
      hw1, hw2, hlsum, hlsumM, hpack28, h28, h57, wtBits]
  · have haux : w2 < 2 ^ 29 := by
      simp only [wtBits] at hw2Bound
      omega
    have hb := payload_bounds w1 w2 mode hw1Bound haux hmodeBound
    have hw2M : w2 % M = w2 := Nat.mod_eq_of_lt hb.2.1
    have hpackM :
        (w1 + (w2 <<< wtBits) + (mode <<< 57)) % M =
          w1 + (w2 <<< wtBits) + (mode <<< 57) :=
      Nat.mod_eq_of_lt hb.2.2.2.2.2.2
    have hpack28 :
        (w1 + (w2 <<< 28) + (mode <<< 57)) % M =
          w1 + (w2 <<< 28) + (mode <<< 57) := by
      simpa only [wtBits] using hpackM
    simp [classPayloadInstrs, LeanCompCert.Verified.InstrBlock.srun,
      RegState.set, sdest, sval, denoteOperand, denoteOp, hm3, hmode,
      hw1, hw2, hlsum, hw2M, hpack28, h28, h57, hzero, wtBits]

private theorem classifyPlanes_machine_facts (x : ClassInput) :
    let pure := classifyPlanes x
    let m := if pure.qualifies then pure.mode else 0
    let m1 := if pure.mode = 1 then 1 else 0
    let m2 := if pure.mode = 2 then 1 else 0
    let m3 := if pure.mode = 3 then 1 else 0
    m ≤ 3 ∧ m1 + 2 * m2 + 3 * m3 = m ∧
      (if m3 = 1 then x.w2 else x.lsum) = pure.aux ∧
      pure.first = x.w1 := by
  cases x with
  | mk large count w1 w2 lsum =>
      cases large <;>
        by_cases h0 : count = 0 <;>
        by_cases h1 : count = 1 <;>
        by_cases h2 : count = 2 <;>
        simp_all [classifyPlanes]

/-- Scalar-machine form of the selector refinement.  It is proved by
composing the three small stages, so elaboration never constructs the
full 24-write state tower. -/
theorem classSelectorInstrs_run (k : Nat) (s : RegState) (x : ClassInput)
    (active : Nat)
    (hlarge : s 95 = if x.large then 1 else 0)
    (hcount : s 96 = x.count)
    (hw1 : s 97 = x.w1) (hw2 : s 99 = x.w2)
    (hlsum : s 91 = x.lsum) (hactive : s 9 = active)
    (hcountBound : x.count ≤ 2)
    (hw1Bound : x.w1 < 2 ^ wtBits)
    (hw2Bound : x.w2 < 2 ^ wtBits)
    (hlsumBound : x.lsum < 2 ^ 29)
    (hactiveBit : active ≤ 1) :
    let out := LeanCompCert.Verified.InstrBlock.srun k s classSelectorInstrs
    (out 115, out 120, out 116, out 128) =
      (classifyPlanes x).machineResult active := by
  let t1 := LeanCompCert.Verified.InstrBlock.srun k s classFlagInstrs
  let t2 := LeanCompCert.Verified.InstrBlock.srun k t1 classModeInstrs
  let t3 := LeanCompCert.Verified.InstrBlock.srun k t2 classPayloadInstrs
  let pure := classifyPlanes x
  let q := if pure.qualifies then 1 else 0
  let m1 := if pure.mode = 1 then 1 else 0
  let m2 := if pure.mode = 2 then 1 else 0
  let m3 := if pure.mode = 3 then 1 else 0
  let mode := if pure.qualifies then pure.mode else 0
  have hf := classFlagInstrs_run k s x active hlarge hcount hactive
    hcountBound hactiveBit
  change flagResult t1 = (m1, m2, m3, q, q * active,
    if x.large then 0 else 1) at hf
  simp only [flagResult, Prod.mk.injEq] at hf
  rcases hf with ⟨h110, h111, h112, h115, h116, _h108⟩
  have facts := classifyPlanes_machine_facts x
  change mode ≤ 3 ∧ m1 + 2 * m2 + 3 * m3 = mode ∧
    (if m3 = 1 then x.w2 else x.lsum) = pure.aux ∧
    pure.first = x.w1 at facts
  have hm1 : m1 ≤ 1 := by unfold m1; split <;> omega
  have hm2 : m2 ≤ 1 := by unfold m2; split <;> omega
  have hm3 : m3 ≤ 1 := by unfold m3; split <;> omega
  have hmode : t2 120 = mode := by
    have hrun := classModeInstrs_run k t1 m1 m2 m3 h110 h111 h112
      hm1 hm2 hm3
    change t2 120 = m1 + 2 * m2 + 3 * m3 at hrun
    exact hrun.trans facts.2.1
  have frameMode (r : Nat)
      (h : LeanCompCert.Verified.RegFrame.writes r classModeInstrs = false) :
      t2 r = t1 r :=
    LeanCompCert.Verified.RegFrame.srun_frame k r classModeInstrs h t1
  have frameFlag (r : Nat)
      (h : LeanCompCert.Verified.RegFrame.writes r classFlagInstrs = false) :
      t1 r = s r :=
    LeanCompCert.Verified.RegFrame.srun_frame k r classFlagInstrs h s
  have ht2w1 : t2 97 = x.w1 :=
    (frameMode 97 (by rfl)).trans ((frameFlag 97 (by rfl)).trans hw1)
  have ht2w2 : t2 99 = x.w2 :=
    (frameMode 99 (by rfl)).trans ((frameFlag 99 (by rfl)).trans hw2)
  have ht2lsum : t2 91 = x.lsum :=
    (frameMode 91 (by rfl)).trans ((frameFlag 91 (by rfl)).trans hlsum)
  have ht2m3 : t2 112 = m3 := (frameMode 112 (by rfl)).trans h112
  have hpayload : t3 128 =
      x.w1 + (pure.aux <<< wtBits) + (mode <<< 57) := by
    have hrun := classPayloadInstrs_run k t2 m3 mode x.w1 x.w2 x.lsum
      ht2m3 hmode ht2w1 ht2w2 ht2lsum hm3 facts.1 hw1Bound hw2Bound
      hlsumBound
    change t3 128 = x.w1 +
      ((if m3 = 1 then x.w2 else x.lsum) <<< wtBits) +
        (mode <<< 57) at hrun
    rw [hrun, facts.2.2.1]
  have framePayload (r : Nat)
      (h : LeanCompCert.Verified.RegFrame.writes r classPayloadInstrs = false) :
      t3 r = t2 r :=
    LeanCompCert.Verified.RegFrame.srun_frame k r classPayloadInstrs h t2
  have ht3mode : t3 120 = mode := (framePayload 120 (by rfl)).trans hmode
  have ht3q : t3 115 = q :=
    (framePayload 115 (by rfl)).trans ((frameMode 115 (by rfl)).trans h115)
  have ht3push : t3 116 = q * active :=
    (framePayload 116 (by rfl)).trans ((frameMode 116 (by rfl)).trans h116)
  change (t3 115, t3 120, t3 116, t3 128) = pure.machineResult active
  rw [ht3q, ht3mode, ht3push, hpayload]
  unfold ClassResult.machineResult
  change (q, mode, q * active,
    x.w1 + (pure.aux <<< wtBits) + (mode <<< 57)) =
      (q, mode, q * active,
        pure.first + (pure.aux <<< wtBits) + (mode <<< 57))
  rw [facts.2.2.2]

/-- The emitted selector implements the pure four-way classifier.  The input
count is saturated to `0`, `1`, or `2`; weights fit their packed fields. -/
theorem classSelectorBody_run (k : Nat) (s : AState) (x : ClassInput)
    (active : Nat)
    (hlarge : s.regs 95 = if x.large then 1 else 0)
    (hcount : s.regs 96 = x.count)
    (hw1 : s.regs 97 = x.w1) (hw2 : s.regs 99 = x.w2)
    (hlsum : s.regs 91 = x.lsum) (hactive : s.regs 9 = active)
    (hcountBound : x.count ≤ 2)
    (hw1Bound : x.w1 < 2 ^ wtBits)
    (hw2Bound : x.w2 < 2 ^ wtBits)
    (hlsumBound : x.lsum < 2 ^ 29)
    (hactiveBit : active ≤ 1) :
    selectorResult (arun k s classSelectorBody) =
      (classifyPlanes x).machineResult active := by
  unfold selectorResult classSelectorBody
  rw [arun_lift_regs]
  exact classSelectorInstrs_run k s.regs x active hlarge hcount hw1 hw2
    hlsum hactive hcountBound hw1Bound hw2Bound hlsumBound hactiveBit

#print axioms classSelectorBody_run
#print axioms mode0_jumpFactors
#print axioms mode1_jumpFactors
#print axioms mode2_jumpFactors
#print axioms mode3_jumpFactors

end LeanCompCert.Ports.R2SegSieve

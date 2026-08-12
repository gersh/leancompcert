import LeanCompCert.Ports.R2SegLnFixConvert

/-!
# Exact stream-payload decoding in the `R₂*` log phase

The classifier stores `(first, aux, mode)` in disjoint 28/29/2-bit fields.
This file proves that the literal production shifts and masks recover those
fields, both where the mode controls the logarithm schedule and where the
jump-factor selector consumes the two weights.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.InstrBlock

/-- The mode load at instruction 242. -/
def logModeInstrs : List Instr :=
  [ .binop 242 .lshr (.reg rPl) (.lit 57) ]

def logModeBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift logModeInstrs

theorem logModeBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 52).take 1 = logModeBody := by
  rfl

/-- The weight-field loads at instructions 263--265. -/
def logPayloadDecodeInstrs : List Instr :=
  [ .binop 263 .band (.reg rPl) (.lit maskWt)
  , .binop 264 .lshr (.reg rPl) (.lit wtBits)
  , .binop 265 .band (.reg 264) (.lit maskAux) ]

def logPayloadDecodeBody : List AInstr :=
  LeanCompCert.Verified.ArrayScalarBlock.lift logPayloadDecodeInstrs

theorem logPayloadDecodeBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 74).take 3 = logPayloadDecodeBody := by
  rfl

private theorem decode_mixed_radix (first aux mode B C : Nat)
    (hB : 0 < B) (hC : 0 < C) (hfirst : first < B) (haux : aux < C) :
    let payload := first + B * (aux + C * mode)
    payload / (B * C) = mode ∧ payload % B = first ∧
      (payload / B) % C = aux := by
  dsimp only
  have hfirstDiv : first / B = 0 := Nat.div_eq_of_lt hfirst
  have hauxDiv : aux / C = 0 := Nat.div_eq_of_lt haux
  have hdivB : (first + B * (aux + C * mode)) / B = aux + C * mode := by
    rw [Nat.add_mul_div_left first (aux + C * mode) hB,
      hfirstDiv, Nat.zero_add]
  constructor
  · rw [← Nat.div_div_eq_div_mul, hdivB]
    rw [Nat.add_mul_div_left aux mode hC, hauxDiv, Nat.zero_add]
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hfirst]
  · rw [hdivB, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt haux]

private theorem pack_reassoc (first aux mode B C : Nat) :
    first + aux * B + mode * (B * C) =
      first + B * (aux + C * mode) := by
  calc
    first + aux * B + mode * (B * C) =
        first + B * aux + B * (C * mode) := by
      rw [Nat.mul_comm aux B, Nat.mul_comm mode (B * C), Nat.mul_assoc]
    _ = first + B * (aux + C * mode) := by
      rw [Nat.mul_add, ← Nat.add_assoc]

private theorem add_mul_succ (B q : Nat) :
    B + B * q = B * (q + 1) := by
  rw [Nat.mul_add, Nat.mul_one]
  exact Nat.add_comm _ _

/-- Arithmetic statement of the production bit-field layout. -/
theorem decode_log_payload (first aux mode : Nat)
    (hfirst : first < 2 ^ wtBits) (haux : aux < 2 ^ 29)
    (_hmode : mode ≤ 3) :
    let payload := first + (aux <<< wtBits) + (mode <<< 57)
    payload >>> 57 = mode ∧
      payload &&& maskWt = first ∧
      (payload >>> wtBits) &&& maskAux = aux := by
  have h57 : 2 ^ 57 = (2 ^ wtBits) * (2 ^ 29) := by
    simp [wtBits]
  have hpack :
      first + (aux <<< wtBits) + (mode <<< 57) =
        first + (2 ^ wtBits) * (aux + (2 ^ 29) * mode) := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, h57]
    exact pack_reassoc first aux mode (2 ^ wtBits) (2 ^ 29)
  have h := decode_mixed_radix first aux mode (2 ^ wtBits) (2 ^ 29)
    (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)) hfirst haux
  dsimp only at h ⊢
  rw [hpack, Nat.shiftRight_eq_div_pow, h57]
  constructor
  · exact h.1
  constructor
  · change _ &&& (2 ^ wtBits - 1) = first
    exact (Nat.and_two_pow_sub_one_eq_mod _ _).trans h.2.1
  · change _ &&& (2 ^ 29 - 1) = aux
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.and_two_pow_sub_one_eq_mod _ _).trans h.2.2

private theorem mixed_payload_lt (first aux mode B C limit : Nat)
    (hfirst : first < B) (haux : aux < C) (hmode : mode ≤ 3)
    (hcap : B * (C * 4) < limit) :
    first + B * (aux + C * mode) < limit := by
  have hq : aux + C * mode < C * 4 := by
    calc
      aux + C * mode < C + C * mode := Nat.add_lt_add_right haux _
      _ = C * (mode + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ C * 4 := Nat.mul_le_mul_left C (by omega)
  calc
    first + B * (aux + C * mode) <
        B + B * (aux + C * mode) := Nat.add_lt_add_right hfirst _
    _ = B * ((aux + C * mode) + 1) :=
      add_mul_succ B (aux + C * mode)
    _ ≤ B * (C * 4) :=
      Nat.mul_le_mul_left B (Nat.succ_le_iff.mpr hq)
    _ < limit := hcap

private theorem log_payload_lt_M (first aux mode : Nat)
    (hfirst : first < 2 ^ wtBits) (haux : aux < 2 ^ 29)
    (hmode : mode ≤ 3) :
    first + (aux <<< wtBits) + (mode <<< 57) < M := by
  have hBC : (2 ^ wtBits) * (2 ^ 29) = 2 ^ 57 := by
    simp only [wtBits]
  have hpack :
      first + (aux <<< wtBits) + (mode <<< 57) =
        first + (2 ^ wtBits) * (aux + (2 ^ 29) * mode) := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, ← hBC]
    exact pack_reassoc first aux mode (2 ^ wtBits) (2 ^ 29)
  rw [hpack]
  apply mixed_payload_lt first aux mode (2 ^ wtBits) (2 ^ 29) M
    hfirst haux hmode
  calc
    2 ^ wtBits * (2 ^ 29 * 4) =
        (2 ^ wtBits * 2 ^ 29) * 4 := by rw [Nat.mul_assoc]
    _ = 2 ^ 57 * 4 := by rw [hBC]
    _ = 2 ^ 57 * 2 ^ 2 := by rfl
    _ = 2 ^ 59 := by rw [← Nat.pow_add]
    _ < M := by
      simpa only [M] using
        (Nat.pow_lt_pow_right (a := 2) (m := 59) (n := 64)
          (by decide) (by decide))

theorem logModeInstrs_run (k : Nat) (s : RegState)
    (first aux mode : Nat)
    (hfirst : first < 2 ^ wtBits) (haux : aux < 2 ^ 29)
    (hmode : mode ≤ 3)
    (hpl : s rPl = first + (aux <<< wtBits) + (mode <<< 57)) :
    (srun k s logModeInstrs) 242 = mode := by
  have hdecode := decode_log_payload first aux mode hfirst haux hmode
  dsimp only at hdecode
  have h57 : (57 : Nat) % M = 57 := by decide
  have hmodeM : mode < M := Nat.lt_of_le_of_lt hmode (by decide)
  simp [logModeInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hpl, h57, hdecode.1,
    Nat.mod_eq_of_lt hmodeM]

theorem logModeBody_run (k : Nat) (s : AState)
    (first aux mode : Nat)
    (hfirst : first < 2 ^ wtBits) (haux : aux < 2 ^ 29)
    (hmode : mode ≤ 3)
    (hpl : s.regs rPl = first + (aux <<< wtBits) + (mode <<< 57)) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s logModeBody
    out.regs 242 = mode ∧ out.arr = s.arr := by
  rw [logModeBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨logModeInstrs_run k s.regs first aux mode
    hfirst haux hmode hpl, rfl⟩

theorem logPayloadDecodeInstrs_run (k : Nat) (s : RegState)
    (first aux mode : Nat)
    (hfirst : first < 2 ^ wtBits) (haux : aux < 2 ^ 29)
    (hmode : mode ≤ 3)
    (hpl : s rPl = first + (aux <<< wtBits) + (mode <<< 57)) :
    let out := srun k s logPayloadDecodeInstrs
    out 263 = first ∧ out 265 = aux := by
  have hdecode := decode_log_payload first aux mode hfirst haux hmode
  dsimp only at hdecode
  have hrPl263 : rPl ≠ 263 := by decide
  have h28 : (wtBits : Nat) % M = wtBits := by decide
  have hmaskWt : maskWt % M = maskWt := by decide
  have hmaskAux : maskAux % M = maskAux := by decide
  have hfirstM : first < M := by
    exact Nat.lt_trans hfirst (by decide)
  have hauxM : aux < M := Nat.lt_trans haux (by decide)
  have hpayloadM := log_payload_lt_M first aux mode hfirst haux hmode
  have hshiftM :
      (first + (aux <<< wtBits) + (mode <<< 57)) >>> wtBits < M :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hpayloadM
  simp [logPayloadDecodeInstrs, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, hpl, hrPl263, h28, hmaskWt, hmaskAux,
    hdecode.2.1, hdecode.2.2, Nat.mod_eq_of_lt hfirstM,
    Nat.mod_eq_of_lt hauxM, Nat.mod_eq_of_lt hshiftM]

/-- Array-state wrapper for the two payload fields used by the factor block. -/
theorem logPayloadDecodeBody_run (k : Nat) (s : AState)
    (first aux mode : Nat)
    (hfirst : first < 2 ^ wtBits) (haux : aux < 2 ^ 29)
    (hmode : mode ≤ 3)
    (hpl : s.regs rPl = first + (aux <<< wtBits) + (mode <<< 57)) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s logPayloadDecodeBody
    out.regs 263 = first ∧ out.regs 265 = aux ∧ out.arr = s.arr := by
  have hrun := logPayloadDecodeInstrs_run k s.regs first aux mode
    hfirst haux hmode hpl
  dsimp only at hrun ⊢
  rw [logPayloadDecodeBody, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨hrun.1, hrun.2, rfl⟩

/-- The decoder and classifier-factor selector are one exact adjacent
production slice. -/
theorem logDecodeThroughFactorBody_eq_slice (c : R2Cfg) :
    (c.logBody.drop 74).take 16 =
      logPayloadDecodeBody ++ logFactorBody := by
  rfl

/-- End-to-end payload-to-factor transition through instructions 263--278. -/
theorem logDecodeThroughFactorBody_run (k : Nat) (s : AState)
    (first aux mode lnN : Nat)
    (hmode : mode ≤ 3) (hmode0 : mode = 0 → first = 0)
    (hfirst : first < 2 ^ wtBits) (haux29 : aux < 2 ^ 29)
    (hpl : s.regs rPl = first + (aux <<< wtBits) + (mode <<< 57))
    (h242 : s.regs 242 = mode)
    (h243 : s.regs 243 = if 2 ≤ mode then 1 else 0)
    (h262 : s.regs 262 = lnN)
    (haux : aux ≤ lnN) (hlnM : lnN < M)
    (hfirstM : first < M) (hauxM : aux < M)
    (hsumM : first + (lnN - aux) < M) :
    let out := LeanCompCert.Verified.ArrayFoldBridge.arun k s
      (logPayloadDecodeBody ++ logFactorBody)
    (out.regs 266 == 1, out.regs 272, out.regs 278) =
        ClassResult.jumpFactors ⟨true, mode, first, aux⟩ lnN ∧
      out.arr = s.arr := by
  rw [LeanCompCert.Verified.ArrayFoldBridge.arun_append]
  let decoded := LeanCompCert.Verified.ArrayFoldBridge.arun k s
    logPayloadDecodeBody
  have hd := logPayloadDecodeBody_run k s first aux mode
    hfirst haux29 hmode hpl
  dsimp only at hd
  have frame (r : Nat)
      (h : LeanCompCert.Verified.ArrayRegFrame.writes r
        logPayloadDecodeBody = false) :
      decoded.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k r logPayloadDecodeBody h s
  have hf := logFactorBody_run k decoded mode first aux lnN
    hmode hmode0 ((frame 242 (by rfl)).trans h242)
    ((frame 243 (by rfl)).trans h243) hd.1 hd.2.1
    ((frame 262 (by rfl)).trans h262) haux hlnM hfirstM hauxM hsumM
  dsimp only at hf ⊢
  exact ⟨hf.1, hf.2.trans hd.2.2⟩

#print axioms decode_log_payload
#print axioms logModeBody_eq_slice
#print axioms logModeInstrs_run
#print axioms logModeBody_run
#print axioms logPayloadDecodeBody_eq_slice
#print axioms logPayloadDecodeInstrs_run
#print axioms logPayloadDecodeBody_run
#print axioms logDecodeThroughFactorBody_eq_slice
#print axioms logDecodeThroughFactorBody_run

end LeanCompCert.Ports.R2SegSieve

import LeanCompCert.Ports.Prop1224CellMarkInstr

/-!
# Literal three-plane update for the Proposition 12.2.4 marker

The exact 16-instruction slice is proved in four small stages.  This avoids
building a large simplifier term while retaining a definitional link to the
production instruction list.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.InstrBlock

def p1224MarkFactorInstrs : List Instr :=
  [ .binop 33 .sub (.reg rBp) (.lit 1)
  , .binop 34 .mul (.reg rFs) (.reg 33)
  , .binop 35 .add (.reg 34) (.lit 1)
  , .binop 36 .sub (.reg rBp) (.lit 2)
  , .binop 37 .mul (.reg rFs) (.reg 36)
  , .binop 38 .add (.reg 37) (.lit 1)
  , .binop 39 .sub (.lit 1) (.reg rFs) ]

def p1224MarkFactorBody : List AInstr := lift p1224MarkFactorInstrs

def p1224MarkRadicalBody : List AInstr :=
  [ .load 40 30
  , .scalar (.binop 41 .mul (.reg 40) (.reg 35))
  , .store 30 41 ]

def p1224MarkPhiBody : List AInstr :=
  [ .load 42 31
  , .scalar (.binop 43 .mul (.reg 42) (.reg 38))
  , .store 31 43 ]

def p1224MarkSqfBody : List AInstr :=
  [ .load 44 32
  , .scalar (.binop 45 .bor (.reg 44) (.reg 39))
  , .store 32 45 ]

def p1224MarkCellBody : List AInstr :=
  p1224MarkFactorBody ++ p1224MarkRadicalBody ++
    p1224MarkPhiBody ++ p1224MarkSqfBody

theorem p1224MarkCellBody_eq_slice (c : CellCfg) :
    (c.markBody.drop 28).take p1224MarkCellBody.length =
      p1224MarkCellBody := by
  rfl

private theorem p1224_or_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ||| b < M :=
  Nat.bitwise_lt_two_pow (n := 64) ha hb

theorem p1224MarkFactorBody_run (k : Nat) (s : AState)
    (p : Nat) (first : Bool) (hp : s.regs rBp = p)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp2 : 2 ≤ p) (hpM : p < M) :
    let out := arun k s p1224MarkFactorBody
    out.regs 35 = (if first then p else 1) ∧
      out.regs 38 = (if first then p - 1 else 1) ∧
      out.regs 39 = (if first then 0 else 1) ∧
      out.regs 30 = s.regs 30 ∧ out.regs 31 = s.regs 31 ∧
      out.regs 32 = s.regs 32 ∧ out.arr = s.arr := by
  have hbp : s.regs 170 = p := by simpa [rBp] using hp
  have hp1M : p - 1 < M := by omega
  have hp2M : p - 2 < M := by omega
  have hsubP1 : (p + (M - 1)) % M = p - 1 := by
    rw [show p + (M - 1) = M + (p - 1) by omega, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hp1M]
  have hsubP2 : (p + (M - 2)) % M = p - 2 := by
    rw [show p + (M - 2) = M + (p - 2) by omega, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hp2M]
  have hpFactor : (p - 1 + 1) % M = p := by
    rw [show p - 1 + 1 = p by omega, Nat.mod_eq_of_lt hpM]
  have hphiFactor : (p - 2 + 1) % M = p - 1 := by
    rw [show p - 2 + 1 = p - 1 by omega, Nat.mod_eq_of_lt hp1M]
  have hsubOne : (1 + (M - 1)) % M = 0 := by decide
  have h1mod : 1 % M = 1 := by decide
  have h2mod : 2 % M = 2 := by decide
  have hpMachine : (p + (M - 1 % M) + 1) % M = p := by
    rw [h1mod, show p + (M - 1) + 1 = M + p by omega,
      Nat.add_mod]
    simp [Nat.mod_eq_of_lt hpM]
  have hphiMachine : (p + (M - 2 % M) + 1) % M = p - 1 := by
    rw [h2mod, show p + (M - 2) + 1 = M + (p - 1) by omega,
      Nat.add_mod]
    simp [Nat.mod_eq_of_lt hp1M]
  cases first with
  | false =>
      have hfs : s.regs 172 = 0 := by simpa [rFs] using hfirst
      simp only [p1224MarkFactorBody, arun_lift]
      simp [p1224MarkFactorInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, hbp, hfs, rBp, rFs, hsubP1, hsubP2,
        hpFactor, hphiFactor, hsubOne, h1mod, h2mod, hpMachine,
        hphiMachine]
  | true =>
      have hfs : s.regs 172 = 1 := by simpa [rFs] using hfirst
      simp only [p1224MarkFactorBody, arun_lift]
      simp [p1224MarkFactorInstrs, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, hbp, hfs, rBp, rFs, hsubP1, hsubP2,
        hpFactor, hphiFactor, hsubOne, h1mod, h2mod, hpMachine,
        hphiMachine]

theorem p1224MarkRadicalBody_run (k : Nat) (s : AState)
    (a word factor : Nat) (ha : s.regs 30 = a)
    (hfactor : s.regs 35 = factor) (hword : s.arr a = word)
    (hvalue : word * factor < M) :
    (arun k s p1224MarkRadicalBody).arr =
      (s.writeArr a (word * factor)).arr := by
  simp [p1224MarkRadicalBody, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, denoteOp, ha, hfactor,
    hword, Nat.mod_eq_of_lt hvalue]

theorem p1224MarkPhiBody_run (k : Nat) (s : AState)
    (a word factor : Nat) (ha : s.regs 31 = a)
    (hfactor : s.regs 38 = factor) (hword : s.arr a = word)
    (hvalue : word * factor < M) :
    (arun k s p1224MarkPhiBody).arr =
      (s.writeArr a (word * factor)).arr := by
  simp [p1224MarkPhiBody, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, denoteOp, ha, hfactor,
    hword, Nat.mod_eq_of_lt hvalue]

theorem p1224MarkSqfBody_run (k : Nat) (s : AState)
    (a word bit : Nat) (ha : s.regs 32 = a)
    (hbit : s.regs 39 = bit) (hword : s.arr a = word)
    (hwordM : word < M) (hbitM : bit < M) :
    (arun k s p1224MarkSqfBody).arr =
      (s.writeArr a (word ||| bit)).arr := by
  have hor : word ||| bit < M := p1224_or_lt_M hwordM hbitM
  simp [p1224MarkSqfBody, arun, astep, AState.writeReg,
    AState.writeArr, sdest, sval, denoteOperand, denoteOp, ha, hbit,
    hword, Nat.mod_eq_of_lt hor]

theorem p1224MarkCellBody_markPower_run (k : Nat) (s : AState)
    (x : P1224MarkCell) (L j p : Nat) (first : Bool)
    (hL : 0 < L)
    (h30 : s.regs 30 = j) (h31 : s.regs 31 = j + L)
    (h32 : s.regs 32 = j + 2 * L)
    (hloaded : p1224PlaneWordsAt s L j = x.encode)
    (hp : s.regs rBp = p)
    (hfirst : s.regs rFs = if first then 1 else 0)
    (hp2 : 2 ≤ p) (hpM : p < M)
    (hrad : x.radical * (if first then p else 1) < M)
    (hphi : x.phiSmall * (if first then p - 1 else 1) < M)
    (hsqfBit : x.sqf ≤ 1) (hsqf : x.sqf < M) :
    let out := arun k s p1224MarkCellBody
    out.arr =
      (writeP1224PlaneWordsAt s L j
        ((x.markPower p first).encode)).arr := by
  let factored := arun k s p1224MarkFactorBody
  let radicalOut := arun k factored p1224MarkRadicalBody
  let phiOut := arun k radicalOut p1224MarkPhiBody
  let out := arun k phiOut p1224MarkSqfBody
  have hf := p1224MarkFactorBody_run k s p first hp hfirst hp2 hpM
  dsimp only at hf
  rcases hf with ⟨hf35, hf38, hf39, hf30, hf31, hf32, hfarr⟩
  have hradWord : s.arr j = x.radical := by
    simpa [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.radical hloaded
  have hphiWord : s.arr (j + L) = x.phiSmall := by
    simpa [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.phiSmall hloaded
  have hsqfWord : s.arr (j + 2 * L) = x.sqf := by
    simpa [p1224PlaneWordsAt, P1224MarkCell.encode] using
      congrArg P1224PlaneWords.sqf hloaded
  have hradArr : radicalOut.arr =
      (factored.writeArr j
        (x.radical * (if first then p else 1))).arr :=
    p1224MarkRadicalBody_run k factored j x.radical
      (if first then p else 1)
      (hf30.trans h30) hf35 (by rw [hfarr]; exact hradWord) hrad
  have hrad31 : radicalOut.regs 31 = factored.regs 31 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k 31
      p1224MarkRadicalBody (by rfl) factored
  have hrad32 : radicalOut.regs 32 = factored.regs 32 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k 32
      p1224MarkRadicalBody (by rfl) factored
  have hrad38 : radicalOut.regs 38 = factored.regs 38 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k 38
      p1224MarkRadicalBody (by rfl) factored
  have hrad39 : radicalOut.regs 39 = factored.regs 39 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k 39
      p1224MarkRadicalBody (by rfl) factored
  have hphiAt : radicalOut.arr (j + L) = x.phiSmall := by
    rw [congrFun hradArr (j + L),
      AState.writeArr_arr_ne _ _ (by omega), hfarr]
    exact hphiWord
  have hphiArr : phiOut.arr =
      (radicalOut.writeArr (j + L)
        (x.phiSmall * (if first then p - 1 else 1))).arr :=
    p1224MarkPhiBody_run k radicalOut (j + L) x.phiSmall
      (if first then p - 1 else 1)
      (hrad31.trans (hf31.trans h31)) (hrad38.trans hf38) hphiAt hphi
  have hphi32 : phiOut.regs 32 = radicalOut.regs 32 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k 32
      p1224MarkPhiBody (by rfl) radicalOut
  have hphi39 : phiOut.regs 39 = radicalOut.regs 39 :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k 39
      p1224MarkPhiBody (by rfl) radicalOut
  have hsqfAt : phiOut.arr (j + 2 * L) = x.sqf := by
    rw [congrFun hphiArr (j + 2 * L),
      AState.writeArr_arr_ne _ _ (by omega),
      congrFun hradArr (j + 2 * L),
      AState.writeArr_arr_ne _ _ (by omega), hfarr]
    exact hsqfWord
  have hbitM : (if first then 0 else 1) < M := by
    cases first <;> decide
  have houtArr : out.arr =
      (phiOut.writeArr (j + 2 * L)
        (x.sqf ||| (if first then 0 else 1))).arr :=
    p1224MarkSqfBody_run k phiOut (j + 2 * L) x.sqf
      (if first then 0 else 1)
      (hphi32.trans (hrad32.trans (hf32.trans h32)))
      (hphi39.trans (hrad39.trans hf39)) hsqfAt hsqf hbitM
  have hsqfNext : x.sqf ||| (if first then 0 else 1) =
      (x.markPower p first).sqf := by
    cases first
    · have hx : x.sqf = 0 ∨ x.sqf = 1 := by omega
      rcases hx with hx | hx <;> simp [hx, P1224MarkCell.markPower]
    · simp [P1224MarkCell.markPower]
  simp only [p1224MarkCellBody, arun_append]
  change out.arr = _
  rw [houtArr, hsqfNext]
  apply funext
  intro a
  simp only [AState.writeArr, writeP1224PlaneWordsAt,
    P1224MarkCell.encode]
  by_cases ha2 : a = j + 2 * L
  · simp [ha2]
  · simp only [if_neg ha2]
    rw [congrFun hphiArr a]
    simp only [AState.writeArr]
    by_cases ha1 : a = j + L
    · simp only [ha1, if_pos]
      cases first <;> simp [P1224MarkCell.markPower]
    · simp only [if_neg ha1]
      rw [congrFun hradArr a]
      simp only [AState.writeArr]
      by_cases ha0 : a = j
      · simp only [ha0, if_pos]
        cases first <;> simp [P1224MarkCell.markPower]
      · simp only [if_neg ha0]
        exact congrFun hfarr a

#print axioms p1224MarkFactorBody_run
#print axioms p1224MarkRadicalBody_run
#print axioms p1224MarkPhiBody_run
#print axioms p1224MarkSqfBody_run
#print axioms p1224MarkCellBody_markPower_run

end LeanCompCert.Ports.Prop1224Cell

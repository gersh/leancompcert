import LeanCompCert.Ports.R2RuntimeMarkDenote
import LeanCompCert.Ports.LogFixRoundSemantics
import LeanCompCert.Ports.R2SegLnFixConvert
import LeanCompCert.Verified.InstrRename

/-! # Source semantics of the compiled R2 fixed-log table packer -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.LogFixed
open LeanCompCert.Verified.InstrRename

def rootPackN (index : Nat) : Nat := index / runtimeScale + 2
def rootPackRound (index : Nat) : Nat := index % runtimeScale

theorem rootPack_index_bounds {index : Nat}
    (hi : index < (runtimeRoot - 1) * runtimeScale) :
    index < M ∧ rootPackN index ≤ runtimeRoot ∧
      rootPackRound index < runtimeScale := by
  have hs : 0 < runtimeScale := by decide
  have hq : index / runtimeScale < runtimeRoot - 1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hi)
  have hr := Nat.mod_lt index hs
  simp [rootPackN, rootPackRound, runtimeRoot, runtimeScale] at hq hr ⊢
  constructor
  · exact Nat.lt_trans hi (by decide)
  constructor <;> omega

theorem rootPackDecode_defined (c : R2Cfg) (index : Nat) (s : AState)
    (hRoot : runtimeRoot < c.arrayLen)
    (hi : index < (r2RootPackProgram c).loopCount) :
    AllDefined c.arrayLen index s rootPackDecode := by
  have hb := rootPack_index_bounds (index := index) (by
    simpa [r2RootPackProgram] using hi)
  have hiM : index % M = index := Nat.mod_eq_of_lt hb.1
  have hsM : runtimeScale % M = runtimeScale := Nat.mod_eq_of_lt (by decide)
  have hsne : runtimeScale % M ≠ 0 := by rw [hsM]; decide
  have hnM : rootPackN index % M = rootPackN index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hb.2.1 (by decide))
  have hncell : rootPackN index < c.arrayLen :=
    Nat.lt_of_le_of_lt hb.2.1 hRoot
  have hnRawM : (index / runtimeScale + 2) % M =
      index / runtimeScale + 2 := by
    simpa [rootPackN] using hnM
  have h24M : 24 % M = 24 := Nat.mod_eq_of_lt (by decide)
  have h24ne : 24 % M ≠ 0 := by rw [h24M]; decide
  have hqM : (index / 24) % M = index / 24 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb.1)
  have hnRaw24M : (index / 24 + 2) % M = index / 24 + 2 := by
    simpa [runtimeScale] using hnRawM
  simp [rootPackDecode, AllDefined, ADefined, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, rootPackN, runtimeScale,
    hiM, hsM, hsne, hnM, hnRawM, hncell]
  constructor
  · exact h24ne
  · rw [if_neg h24ne, Option.getD_some, h24M, hqM, hnRaw24M]
    simpa [rootPackN, runtimeScale] using hncell

theorem rootPackRoundInit_defined (len index : Nat) (s : AState) :
    AllDefined len index s rootPackRoundInit := by
  rw [rootPackRoundInit, AllDefined_append]
  constructor
  · exact LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
      len index rootPackExponentS s (by decide)
  · exact LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
      len index rootPackMantissaInitS _ (by decide)

theorem rootPackLogRound_defined (len index : Nat) (s : AState) :
    AllDefined len index s rootPackLogRound := by
  exact LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
    len index rootPackLogRoundS s (by decide)

theorem rootPackLn_defined (len index : Nat) (s : AState) :
    AllDefined len index s rootPackLn := by
  exact LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
    len index rootPackLnS s (by decide)

/-! ## Relocated fixed-log round -/

/-- Relocate the standalone fixed-log inputs to the packer's persistent
registers and its scratch registers to `27,...,44`. -/
def rootPackLogReg : Nat → Nat
  | 0 => rpXm
  | 1 => rpAa
  | n + 2 => n + 27

theorem rootPackLogReg_injective : Function.Injective rootPackLogReg := by
  intro a b h
  rcases a with (_ | _ | a) <;> rcases b with (_ | _ | b) <;>
    simp [rootPackLogReg, rpXm, rpAa] at h ⊢ <;> omega

theorem rootPackLogRoundS_eq_rename :
    rootPackLogRoundS =
      LeanCompCert.Ports.LogFixPort.logRoundBody.map
        (renameInstr rootPackLogReg) := by
  rfl

/-- The packer's compiled twenty-instruction block is the already verified
fixed-log recurrence, merely under a different register allocation. -/
theorem rootPackLogRoundS_run_of_range (k : Nat) (s : RegState) (x a : Nat)
    (hx : s rpXm = x) (ha : s rpAa = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := srun k s rootPackLogRoundS
    out rpXm = logMant x ∧ out rpAa = (a <<< 1) + logBit x := by
  let base : RegState := fun r => s (rootPackLogReg r)
  have hbase := LeanCompCert.Ports.LogFixPort.logRoundBody_srun_of_range
    k base x a (by
      simpa [base, rootPackLogReg, LeanCompCert.Ports.LogFixPort.rX] using hx)
      (by
        simpa [base, rootPackLogReg, LeanCompCert.Ports.LogFixPort.rA] using ha)
      hxlo hxhi haBound
  have hrename := srun_rename k rootPackLogReg rootPackLogReg_injective
    LeanCompCert.Ports.LogFixPort.logRoundBody base s (by
      intro r
      rfl)
  constructor
  · rw [show rpXm = rootPackLogReg LeanCompCert.Ports.LogFixPort.rX by rfl]
    rw [rootPackLogRoundS_eq_rename]
    exact (hrename LeanCompCert.Ports.LogFixPort.rX).trans hbase.1
  · rw [show rpAa = rootPackLogReg LeanCompCert.Ports.LogFixPort.rA by rfl]
    rw [rootPackLogRoundS_eq_rename]
    exact (hrename LeanCompCert.Ports.LogFixPort.rA).trans hbase.2

theorem rootPackLogRound_run_of_range (k : Nat) (s : AState) (x a : Nat)
    (hx : s.regs rpXm = x) (ha : s.regs rpAa = a)
    (hxlo : B62 ≤ x) (hxhi : x < B63) (haBound : a < B62) :
    let out := arun k s rootPackLogRound
    out.regs rpXm = logMant x ∧
      out.regs rpAa = (a <<< 1) + logBit x ∧ out.arr = s.arr := by
  rw [rootPackLogRound,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := rootPackLogRoundS_run_of_range k s.regs x a
    hx ha hxlo hxhi haBound
  exact ⟨h.1, h.2, rfl⟩

/-! ## Relocated natural-log conversion -/

/-- Swap the conversion block's production registers `251,...,262` with the
packer's compact allocation `46,...,57`, fixing every other register. -/
def rootPackLnReg (n : Nat) : Nat :=
  if n < 46 then n
  else if n < 58 then n + 205
  else if n < 251 then n
  else if n < 263 then n - 205
  else n

theorem rootPackLnReg_injective : Function.Injective rootPackLnReg := by
  intro a b h
  simp only [rootPackLnReg] at h
  repeat' first | split at h
  all_goals omega

theorem rootPackLnConvertS_eq_rename :
    rootPackLnConvertS = lnFixConvertInstrs.map (renameInstr rootPackLnReg) := by
  rfl

theorem rootPackLnConvertS_logFix_run (k : Nat) (s : RegState) (S n : Nat)
    (ha : logFix S n < 2 ^ 30) (h46 : s 46 = logFix S n) :
    (srun k s rootPackLnConvertS) 57 =
      LeanCompCert.Ports.PsiSegSieve.lnFix S n := by
  let base : RegState := fun r => s (rootPackLnReg r)
  have hbase := lnFixConvertInstrs_logFix_run k base S n ha (by
    simpa [base, rootPackLnReg] using h46)
  have hrename := srun_rename k rootPackLnReg rootPackLnReg_injective
    lnFixConvertInstrs base s (by
      intro r
      rfl)
  rw [show (57 : Nat) = rootPackLnReg 262 by rfl]
  rw [rootPackLnConvertS_eq_rename]
  exact (hrename 262).trans hbase

theorem rootPackLnConvert_logFix_run (k : Nat) (s : AState) (S n : Nat)
    (ha : logFix S n < 2 ^ 30) (h46 : s.regs 46 = logFix S n) :
    let out := arun k s
      (LeanCompCert.Verified.ArrayScalarBlock.lift rootPackLnConvertS)
    out.regs 57 = LeanCompCert.Ports.PsiSegSieve.lnFix S n ∧
      out.arr = s.arr := by
  rw [LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackLnConvertS_logFix_run k s.regs S n ha h46, rfl⟩

#print axioms rootPackDecode_defined
#print axioms rootPackRoundInit_defined
#print axioms rootPackLogRound_defined
#print axioms rootPackLn_defined
#print axioms rootPackLogReg_injective
#print axioms rootPackLogRoundS_run_of_range
#print axioms rootPackLogRound_run_of_range
#print axioms rootPackLnReg_injective
#print axioms rootPackLnConvertS_logFix_run
#print axioms rootPackLnConvert_logFix_run

end LeanCompCert.Ports.R2SegSieve

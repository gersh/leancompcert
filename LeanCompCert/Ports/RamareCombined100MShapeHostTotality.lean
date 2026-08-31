import LeanCompCert.Ports.RamareCombined100MHostTotality
import LeanCompCert.Ports.RamareCombined100MPowerCellScheduleInvariant
import LeanCompCert.Ports.RamareCombined100MClassificationInvariant

/-!
# Symbolic totality of the production shape-sieve host

This file cuts the shape sieve at its actual partial instructions.  It does
not evaluate a marking or classification loop.  The two classifier divisors
are discharged from their immediately preceding normalisation prefixes.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

namespace ShapeHost

theorem markLoad_defined (len k : Nat) (s : AState)
    (h30 : s.regs 30 < len) (h31 : s.regs 31 < len)
    (h32 : s.regs 32 < len) (h33 : s.regs 33 < len)
    (h34 : s.regs 34 < len) (h35 : s.regs 35 < len)
    (h36 : s.regs 36 < len) :
    AllDefined len k s ShapeSieve.Cfg.markLoadBody := by
  simp [ShapeSieve.Cfg.markLoadBody, AllDefined, ADefined, astep,
    AState.writeReg, h30, h31, h32, h33, h34, h35, h36]

theorem markCell_defined (len k : Nat) (s : AState)
    (h30 : s.regs 30 < len) (h31 : s.regs 31 < len)
    (h32 : s.regs 32 < len) (h33 : s.regs 33 < len)
    (h34 : s.regs 34 < len) (h35 : s.regs 35 < len)
    (h36 : s.regs 36 < len) :
    AllDefined len k s ShapeSieve.Cfg.markCellBody := by
  simp [ShapeSieve.Cfg.markCellBody, ShapeSieve.Cfg.markAllProductBody,
    ShapeSieve.Cfg.markFirstBody, ShapeSieve.Cfg.markFirstSelectBody,
    ShapeSieve.Cfg.markFirstExponentBody,
    ShapeSieve.Cfg.markFirstProductBody, ShapeSieve.Cfg.markSecondBody,
    ShapeSieve.Cfg.markSecondSelectBody, ShapeSieve.Cfg.markSecondFlagsBody,
    ShapeSieve.Cfg.markSecondCommitBody,
    ShapeSieve.Cfg.markSecondExponentBody,
    ShapeSieve.Cfg.markSecondProductBody, AllDefined, ADefined, astep,
    sdest, sval, denoteOperand, denoteOp, AState.writeReg, AState.writeArr,
    h30, h31, h32, h33, h34, h35, h36]

theorem markReset_defined (c : ShapeSieve.Cfg) (len k : Nat) (s : AState)
    (hp : c.table.headD 1 ≠ 0) (hpM : c.table.headD 1 < M) :
    AllDefined len k s c.markResetBody := by
  cases ht : c.table with
  | nil =>
      have hM1 : M ≠ 1 := by decide
      simp [ShapeSieve.Cfg.markResetBody, AllDefined, ADefined, astep,
        sdest, sval, denoteOperand, denoteOp, AState.writeReg,
        List.headD, ht, hM1] at hpM ⊢
  | cons p ps =>
      have hpmod : p % M = p := by
        apply Nat.mod_eq_of_lt
        simpa [List.headD, ht] using hpM
      have hpne : p ≠ 0 := by simpa [List.headD, ht] using hp
      simp [ShapeSieve.Cfg.markResetBody, AllDefined, ADefined, astep,
        sdest, sval, denoteOperand, denoteOp, AState.writeReg,
        List.headD, ht, hpmod, hpne]

def markAdvanceLoadPrefix (c : ShapeSieve.Cfg) : List AInstr :=
  [.scalar (.binop 95 .add (.reg ShapeSieve.rPi) (.lit c.tableBase))]

theorem markAdvanceLoadBody_eq (c : ShapeSieve.Cfg) :
    c.markAdvanceLoadBody = markAdvanceLoadPrefix c ++ [.load 96 95] := rfl

theorem markAdvanceLoad_defined (c : ShapeSieve.Cfg) (len k : Nat)
    (s : AState)
    (h95 : (arun k s (markAdvanceLoadPrefix c)).regs 95 < len) :
    AllDefined len k s c.markAdvanceLoadBody := by
  let indexed := arun k s (markAdvanceLoadPrefix c)
  have hp : AllDefined len k s (markAdvanceLoadPrefix c) :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have hl : AllDefined len k indexed [.load 96 95] :=
    load_defined len k indexed 96 95 h95
  rw [markAdvanceLoadBody_eq, AllDefined_append]
  simpa only [indexed] using ⟨hp, hl⟩

theorem markAdvanceOffset_defined (c : ShapeSieve.Cfg) (len k : Nat)
    (s : AState) (hpow : s.regs ShapeSieve.rPow ≠ 0) :
    AllDefined len k s c.markAdvanceOffsetBody := by
  have hpow' : s.regs 3 ≠ 0 := by
    simpa only [ShapeSieve.rPow] using hpow
  simp [ShapeSieve.Cfg.markAdvanceOffsetBody, AllDefined, ADefined, astep,
    sdest, sval, denoteOperand, denoteOp, AState.writeReg,
    ShapeSieve.rPow, hpow']

def classTailNormalize : List Instr :=
  [ .binop 164 .eq (.reg 146) (.lit 0)
  , .binop 165 .add (.reg 146) (.reg 164) ]

def classTailFromDiv : List Instr :=
  [ .binop 166 .udiv (.reg ShapeSieve.rShapeRest) (.reg 165)
  , .binop ShapeSieve.rShapeTail .mul (.reg 162) (.reg 166)
  , .binop 167 .sub (.lit 1) (.reg 162)
  , .binop ShapeSieve.rShapeTail .add (.reg ShapeSieve.rShapeTail) (.reg 167) ]

theorem classTailBody_eq :
    ShapeSieve.Cfg.classTailBody = classTailNormalize ++ classTailFromDiv := rfl

theorem nonzeroProduct_ne_zero (x : Nat) (hx : x < M) :
    ShapeSieve.nonzeroProduct x ≠ 0 := by
  unfold ShapeSieve.nonzeroProduct ShapeSieve.zeroBit
  split <;> omega

theorem classNormalize_r152 (k : Nat) (s : AState)
    (h140 : s.regs 140 < M) (h143 : s.regs 143 < M) :
    (arun k s (lift ShapeSieve.Cfg.classNormalizeBody)).regs 152 =
      ShapeSieve.nonzeroProduct (s.regs 143) := by
  simpa using (ShapeSieve.Cfg.classNormalizeBody_run k s
    h140 h143).2.2.2.2.2.1

theorem classTailNormalize_r165 (k : Nat) (s : AState)
    (h146 : s.regs 146 < M) :
    (arun k s (lift classTailNormalize)).regs 165 =
      ShapeSieve.nonzeroProduct (s.regs 146) := by
  rw [arun_lift_regs]
  simp [classTailNormalize, ShapeSieve.nonzeroProduct,
    ShapeSieve.zeroBit, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set]
  split
  · have : 1 % M = 1 := by decide
    simp_all
  · rw [Nat.add_zero, Nat.mod_eq_of_lt h146]

theorem classDecode_defined (len k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M) :
    AllDefined len k s (lift ShapeSieve.Cfg.classDecodeBody) := by
  let normalized := arun k s (lift ShapeSieve.Cfg.classNormalizeBody)
  let first := arun k normalized (lift ShapeSieve.Cfg.classFirstShapeBody)
  let flags := arun k first (lift ShapeSieve.Cfg.classSecondFlagsBody)
  let second := arun k flags (lift ShapeSieve.Cfg.classSecondShapeBody)
  let tailNorm := arun k second (lift classTailNormalize)
  have hnorm : AllDefined len k s
      (lift ShapeSieve.Cfg.classNormalizeBody) :=
    allDefined_lift_of_noDiv len k _ s (by rfl)
  have h152 : normalized.regs 152 ≠ 0 := by
    rw [classNormalize_r152 k s (hw 140) (hw 143)]
    exact nonzeroProduct_ne_zero _ (hw 143)
  have hfirst : AllDefined len k normalized
      (lift ShapeSieve.Cfg.classFirstShapeBody) := by
    apply allDefined_lift_of_divRegCheck len k 152 _ normalized
    · rfl
    · rfl
    · exact h152
  have hflags : AllDefined len k first
      (lift ShapeSieve.Cfg.classSecondFlagsBody) :=
    allDefined_lift_of_noDiv len k _ first (by rfl)
  have hsecond : AllDefined len k flags
      (lift ShapeSieve.Cfg.classSecondShapeBody) :=
    allDefined_lift_of_noDiv len k _ flags (by rfl)
  have hsecondWord := arun_word k
    (((lift ShapeSieve.Cfg.classNormalizeBody ++
       lift ShapeSieve.Cfg.classFirstShapeBody) ++
       lift ShapeSieve.Cfg.classSecondFlagsBody) ++
       lift ShapeSieve.Cfg.classSecondShapeBody) s hw
      ha
  have h146second : second.regs 146 < M := by
    simpa only [normalized, first, flags, second, arun_append] using
      hsecondWord.1 146
  have htailNorm : AllDefined len k second (lift classTailNormalize) :=
    allDefined_lift_of_noDiv len k _ second (by rfl)
  have h165 : tailNorm.regs 165 ≠ 0 := by
    rw [classTailNormalize_r165 k second h146second]
    exact nonzeroProduct_ne_zero _ h146second
  have htailDiv : AllDefined len k tailNorm (lift classTailFromDiv) := by
    apply allDefined_lift_of_divRegCheck len k 165 _ tailNorm
    · rfl
    · rfl
    · exact h165
  have htail : AllDefined len k second
      (lift ShapeSieve.Cfg.classTailBody) := by
    rw [classTailBody_eq, lift_append, AllDefined_append]
    simpa only [tailNorm] using ⟨htailNorm, htailDiv⟩
  let tailed := arun k second (lift ShapeSieve.Cfg.classTailBody)
  have hg1 : AllDefined len k tailed
      (lift ShapeSieve.Cfg.classFirstGuardBody) :=
    allDefined_lift_of_noDiv len k _ tailed (by rfl)
  let guarded1 := arun k tailed (lift ShapeSieve.Cfg.classFirstGuardBody)
  have hg2 : AllDefined len k guarded1
      (lift ShapeSieve.Cfg.classSecondGuardBody) :=
    allDefined_lift_of_noDiv len k _ guarded1 (by rfl)
  let guarded2 := arun k guarded1 (lift ShapeSieve.Cfg.classSecondGuardBody)
  have hg3 : AllDefined len k guarded2
      (lift ShapeSieve.Cfg.classGuardCommitBody) :=
    allDefined_lift_of_noDiv len k _ guarded2 (by rfl)
  have h01 : AllDefined len k s
      (lift ShapeSieve.Cfg.classNormalizeBody ++
        lift ShapeSieve.Cfg.classFirstShapeBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [normalized] using ⟨hnorm, hfirst⟩)
  have h012 : AllDefined len k s
      ((lift ShapeSieve.Cfg.classNormalizeBody ++
        lift ShapeSieve.Cfg.classFirstShapeBody) ++
        lift ShapeSieve.Cfg.classSecondFlagsBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, normalized, first] using ⟨h01, hflags⟩)
  have h0123 : AllDefined len k s
      (((lift ShapeSieve.Cfg.classNormalizeBody ++
        lift ShapeSieve.Cfg.classFirstShapeBody) ++
        lift ShapeSieve.Cfg.classSecondFlagsBody) ++
        lift ShapeSieve.Cfg.classSecondShapeBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, normalized, first, flags] using ⟨h012, hsecond⟩)
  have h01234 : AllDefined len k s
      ((((lift ShapeSieve.Cfg.classNormalizeBody ++
        lift ShapeSieve.Cfg.classFirstShapeBody) ++
        lift ShapeSieve.Cfg.classSecondFlagsBody) ++
        lift ShapeSieve.Cfg.classSecondShapeBody) ++
        lift ShapeSieve.Cfg.classTailBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, normalized, first, flags, second] using
        ⟨h0123, htail⟩)
  have h012345 : AllDefined len k s
      (((((lift ShapeSieve.Cfg.classNormalizeBody ++
        lift ShapeSieve.Cfg.classFirstShapeBody) ++
        lift ShapeSieve.Cfg.classSecondFlagsBody) ++
        lift ShapeSieve.Cfg.classSecondShapeBody) ++
        lift ShapeSieve.Cfg.classTailBody) ++
        lift ShapeSieve.Cfg.classFirstGuardBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, normalized, first, flags, second, tailed] using
        ⟨h01234, hg1⟩)
  have h0123456 : AllDefined len k s
      ((((((lift ShapeSieve.Cfg.classNormalizeBody ++
        lift ShapeSieve.Cfg.classFirstShapeBody) ++
        lift ShapeSieve.Cfg.classSecondFlagsBody) ++
        lift ShapeSieve.Cfg.classSecondShapeBody) ++
        lift ShapeSieve.Cfg.classTailBody) ++
        lift ShapeSieve.Cfg.classFirstGuardBody) ++
        lift ShapeSieve.Cfg.classSecondGuardBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, normalized, first, flags, second, tailed,
        guarded1] using ⟨h012345, hg2⟩)
  have hall : AllDefined len k s
      (((((((lift ShapeSieve.Cfg.classNormalizeBody ++
        lift ShapeSieve.Cfg.classFirstShapeBody) ++
        lift ShapeSieve.Cfg.classSecondFlagsBody) ++
        lift ShapeSieve.Cfg.classSecondShapeBody) ++
        lift ShapeSieve.Cfg.classTailBody) ++
        lift ShapeSieve.Cfg.classFirstGuardBody) ++
        lift ShapeSieve.Cfg.classSecondGuardBody) ++
        lift ShapeSieve.Cfg.classGuardCommitBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, normalized, first, flags, second, tailed,
        guarded1, guarded2] using ⟨h0123456, hg3⟩)
  simpa only [ShapeSieve.Cfg.classDecodeBody, lift_append,
    List.append_assoc] using hall

/-- Exact state-cut obligations for one shape body.  Unlike `AllDefined`,
these fields mention only the dynamic array addresses and cursor power. -/
structure Guards (c : ShapeSieve.Cfg) (len k : Nat) (s : AState) : Prop where
  tableHead_ne : c.table.headD 1 ≠ 0
  tableHead_word : c.table.headD 1 < M
  markAddresses :
    let phased := arun k s (lift c.markPhaseBody)
    let reset := arun k phased c.markResetBody
    let addressed := arun k reset c.markAddressBody
    addressed.regs 30 < len ∧ addressed.regs 31 < len ∧
      addressed.regs 32 < len ∧ addressed.regs 33 < len ∧
      addressed.regs 34 < len ∧ addressed.regs 35 < len ∧
      addressed.regs 36 < len
  tableAddress :
    let phased := arun k s (lift c.markPhaseBody)
    let reset := arun k phased c.markResetBody
    let marked := arun k reset c.markCellPrefix
    let selected := arun k marked c.markAdvanceSelectBody
    (arun k selected (markAdvanceLoadPrefix c)).regs 95 < len
  nextPower_ne :
    let phased := arun k s (lift c.markPhaseBody)
    let reset := arun k phased c.markResetBody
    let marked := arun k reset c.markCellPrefix
    let selected := arun k marked c.markAdvanceSelectBody
    let loaded := arun k selected c.markAdvanceLoadBody
    let valued := arun k loaded ShapeSieve.Cfg.markAdvanceValueBody
    valued.regs ShapeSieve.rPow ≠ 0
  classAddresses :
    let marked := arun k s c.markBody
    let addressed := arun k marked c.classAddressBody
    addressed.regs 131 < len ∧ addressed.regs 133 < len ∧
      addressed.regs 134 < len ∧ addressed.regs 135 < len ∧
      addressed.regs 136 < len ∧ addressed.regs 137 < len ∧
      addressed.regs 138 < len

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem markBody_defined (c : ShapeSieve.Cfg) (len k : Nat) (s : AState)
    (h : Guards c len k s) : AllDefined len k s c.markBody := by
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  let addressed := arun k reset c.markAddressBody
  let loaded := arun k addressed ShapeSieve.Cfg.markLoadBody
  let marked := arun k loaded ShapeSieve.Cfg.markCellBody
  let selected := arun k marked c.markAdvanceSelectBody
  let indexed := arun k selected (markAdvanceLoadPrefix c)
  let nextLoaded := arun k selected c.markAdvanceLoadBody
  let valued := arun k nextLoaded ShapeSieve.Cfg.markAdvanceValueBody
  let offset := arun k valued c.markAdvanceOffsetBody
  have hphase : AllDefined len k s (lift c.markPhaseBody) :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have hreset : AllDefined len k phased c.markResetBody :=
    markReset_defined c len k phased h.tableHead_ne h.tableHead_word
  have haddress : AllDefined len k reset c.markAddressBody :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have hload : AllDefined len k addressed ShapeSieve.Cfg.markLoadBody :=
    markLoad_defined len k addressed h.markAddresses.1
      h.markAddresses.2.1 h.markAddresses.2.2.1
      h.markAddresses.2.2.2.1 h.markAddresses.2.2.2.2.1
      h.markAddresses.2.2.2.2.2.1 h.markAddresses.2.2.2.2.2.2
  have keep (r : Nat) (hw : writes r ShapeSieve.Cfg.markLoadBody = false) :
      loaded.regs r = addressed.regs r :=
    arun_frame k r ShapeSieve.Cfg.markLoadBody hw addressed
  have hcell : AllDefined len k loaded ShapeSieve.Cfg.markCellBody :=
    markCell_defined len k loaded
      (by rw [keep 30 (by rfl)]; exact h.markAddresses.1)
      (by rw [keep 31 (by rfl)]; exact h.markAddresses.2.1)
      (by rw [keep 32 (by rfl)]; exact h.markAddresses.2.2.1)
      (by rw [keep 33 (by rfl)]; exact h.markAddresses.2.2.2.1)
      (by rw [keep 34 (by rfl)]; exact h.markAddresses.2.2.2.2.1)
      (by rw [keep 35 (by rfl)]; exact h.markAddresses.2.2.2.2.2.1)
      (by rw [keep 36 (by rfl)]; exact h.markAddresses.2.2.2.2.2.2)
  have hselect : AllDefined len k marked c.markAdvanceSelectBody :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have htableAddress := h.tableAddress
  change indexed.regs 95 < len at htableAddress
  have hnextLoad : AllDefined len k selected c.markAdvanceLoadBody :=
    markAdvanceLoad_defined c len k selected htableAddress
  have hvalue : AllDefined len k nextLoaded
      ShapeSieve.Cfg.markAdvanceValueBody :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have hnextPower := h.nextPower_ne
  change valued.regs ShapeSieve.rPow ≠ 0 at hnextPower
  have hoffset : AllDefined len k valued c.markAdvanceOffsetBody :=
    markAdvanceOffset_defined c len k valued hnextPower
  have hbudget : AllDefined len k offset c.markBudgetBody :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have h01 : AllDefined len k s
      (lift c.markPhaseBody ++ c.markResetBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [phased] using ⟨hphase, hreset⟩)
  have h012 : AllDefined len k s
      ((lift c.markPhaseBody ++ c.markResetBody) ++ c.markAddressBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, phased, reset] using ⟨h01, haddress⟩)
  have h0123 : AllDefined len k s
      (((lift c.markPhaseBody ++ c.markResetBody) ++ c.markAddressBody) ++
        ShapeSieve.Cfg.markLoadBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, phased, reset, addressed] using ⟨h012, hload⟩)
  have h01234 : AllDefined len k s
      ((((lift c.markPhaseBody ++ c.markResetBody) ++ c.markAddressBody) ++
        ShapeSieve.Cfg.markLoadBody) ++ ShapeSieve.Cfg.markCellBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, phased, reset, addressed, loaded] using
        ⟨h0123, hcell⟩)
  have h012345 : AllDefined len k s
      (((((lift c.markPhaseBody ++ c.markResetBody) ++ c.markAddressBody) ++
        ShapeSieve.Cfg.markLoadBody) ++ ShapeSieve.Cfg.markCellBody) ++
        c.markAdvanceSelectBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, phased, reset, addressed, loaded, marked] using
        ⟨h01234, hselect⟩)
  have h0123456 : AllDefined len k s
      ((((((lift c.markPhaseBody ++ c.markResetBody) ++ c.markAddressBody) ++
        ShapeSieve.Cfg.markLoadBody) ++ ShapeSieve.Cfg.markCellBody) ++
        c.markAdvanceSelectBody) ++ c.markAdvanceLoadBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, phased, reset, addressed, loaded, marked,
        selected] using ⟨h012345, hnextLoad⟩)
  have h01234567 : AllDefined len k s
      (((((((lift c.markPhaseBody ++ c.markResetBody) ++ c.markAddressBody) ++
        ShapeSieve.Cfg.markLoadBody) ++ ShapeSieve.Cfg.markCellBody) ++
        c.markAdvanceSelectBody) ++ c.markAdvanceLoadBody) ++
        ShapeSieve.Cfg.markAdvanceValueBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, phased, reset, addressed, loaded, marked,
        selected, nextLoaded] using ⟨h0123456, hvalue⟩)
  have h0 : AllDefined len k s
      ((((((((lift c.markPhaseBody ++ c.markResetBody) ++
        c.markAddressBody) ++ ShapeSieve.Cfg.markLoadBody) ++
        ShapeSieve.Cfg.markCellBody) ++ c.markAdvanceSelectBody) ++
        c.markAdvanceLoadBody) ++ ShapeSieve.Cfg.markAdvanceValueBody) ++
        c.markAdvanceOffsetBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, phased, reset, addressed, loaded, marked,
        selected, nextLoaded, valued] using ⟨h01234567, hoffset⟩)
  have hall : AllDefined len k s
      (((((((((lift c.markPhaseBody ++ c.markResetBody) ++
        c.markAddressBody) ++ ShapeSieve.Cfg.markLoadBody) ++
        ShapeSieve.Cfg.markCellBody) ++ c.markAdvanceSelectBody) ++
        c.markAdvanceLoadBody) ++ ShapeSieve.Cfg.markAdvanceValueBody) ++
        c.markAdvanceOffsetBody) ++ c.markBudgetBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, phased, reset, addressed, loaded, marked,
        selected, nextLoaded, valued, offset] using ⟨h0, hbudget⟩)
  simpa only [ShapeSieve.Cfg.markBody, ShapeSieve.Cfg.markCoreBody,
    ShapeSieve.Cfg.markAdvanceBody, ShapeSieve.Cfg.markAdvanceCursorBody,
    ShapeSieve.Cfg.markCellPrefix, lift_append, List.append_assoc] using hall

theorem classBody_defined (c : ShapeSieve.Cfg) (len k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (haddr :
      let addressed := arun k s c.classAddressBody
      addressed.regs 131 < len ∧ addressed.regs 133 < len ∧
        addressed.regs 134 < len ∧ addressed.regs 135 < len ∧
        addressed.regs 136 < len ∧ addressed.regs 137 < len ∧
        addressed.regs 138 < len) :
    AllDefined len k s c.classBody := by
  let addressed := arun k s c.classAddressBody
  let loaded := arun k addressed ShapeSieve.Cfg.classLoadBody
  let decoded := arun k loaded (lift ShapeSieve.Cfg.classDecodeBody)
  have haddress : AllDefined len k s c.classAddressBody :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  have hload : AllDefined len k addressed ShapeSieve.Cfg.classLoadBody :=
    ShapeSieve.Cfg.classLoadBody_defined len k addressed haddr.1
      haddr.2.1 haddr.2.2.1 haddr.2.2.2.1 haddr.2.2.2.2.1
      haddr.2.2.2.2.2.1 haddr.2.2.2.2.2.2
  have waddress := arun_word k c.classAddressBody s hw ha
  have wloaded := arun_word k ShapeSieve.Cfg.classLoadBody addressed
    waddress.1 waddress.2
  have hdecode := classDecode_defined len k loaded wloaded.1 wloaded.2
  have keepAddress (r : Nat)
      (hd : writes r (lift ShapeSieve.Cfg.classDecodeBody) = false)
      (hl : writes r ShapeSieve.Cfg.classLoadBody = false) :
      decoded.regs r = addressed.regs r := by
    exact (arun_frame k r (lift ShapeSieve.Cfg.classDecodeBody) hd loaded).trans
      (arun_frame k r ShapeSieve.Cfg.classLoadBody hl addressed)
  have hclear : AllDefined len k decoded ShapeSieve.Cfg.classClearBody :=
    ShapeSieve.Cfg.classClearBody_defined len k decoded
      (by rw [keepAddress 131 (by rfl) (by rfl)]; exact haddr.1)
      (by rw [keepAddress 133 (by rfl) (by rfl)]; exact haddr.2.1)
      (by rw [keepAddress 134 (by rfl) (by rfl)]; exact haddr.2.2.1)
      (by rw [keepAddress 135 (by rfl) (by rfl)]; exact haddr.2.2.2.1)
      (by rw [keepAddress 136 (by rfl) (by rfl)]; exact haddr.2.2.2.2.1)
      (by rw [keepAddress 137 (by rfl) (by rfl)]; exact haddr.2.2.2.2.2.1)
      (by rw [keepAddress 138 (by rfl) (by rfl)]; exact haddr.2.2.2.2.2.2)
  have h01 : AllDefined len k s
      (c.classAddressBody ++ ShapeSieve.Cfg.classLoadBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [addressed] using ⟨haddress, hload⟩)
  have h012 : AllDefined len k s
      ((c.classAddressBody ++ ShapeSieve.Cfg.classLoadBody) ++
        lift ShapeSieve.Cfg.classDecodeBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, addressed, loaded] using ⟨h01, hdecode⟩)
  have hall : AllDefined len k s
      (((c.classAddressBody ++ ShapeSieve.Cfg.classLoadBody) ++
        lift ShapeSieve.Cfg.classDecodeBody) ++
        ShapeSieve.Cfg.classClearBody) :=
    (AllDefined_append len k _ _ s).mpr (by
      simpa only [arun_append, addressed, loaded, decoded] using ⟨h012, hclear⟩)
  simpa only [ShapeSieve.Cfg.classBody, ShapeSieve.Cfg.classAddressBody,
    ShapeSieve.Cfg.classIndexBody, ShapeSieve.Cfg.classPostCandidateBody,
    ShapeSieve.Cfg.classAfterAddressBody, List.append_assoc] using hall

theorem body_defined_of_guards (c : ShapeSieve.Cfg) (len k : Nat)
    (s : AState) (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (h : Guards c len k s) : AllDefined len k s c.body := by
  let marked := arun k s c.markBody
  let classified := arun k marked c.classBody
  have hm := markBody_defined c len k s h
  have wm := arun_word k c.markBody s hw ha
  have hc := classBody_defined c len k marked wm.1 wm.2 h.classAddresses
  have ht : AllDefined len k classified c.tailBody :=
    allDefined_of_all_hostNoPartial len k _ _ (by rfl)
  rw [ShapeSieve.Cfg.body, AllDefined_append, AllDefined_append]
  simpa only [marked, classified, arun_append] using ⟨⟨hm, hc⟩, ht⟩

end ShapeHost

/-- Reduced production-host invariant.  Its shape component contains only
the actual access/divisor cuts, while the arithmetic component reuses the
existing semantic range invariant. -/
structure LambdaPsiSweep.ShapeHostInvariant (c : LambdaPsiSweep.Cfg)
    (k : Nat) (s : AState) : Prop where
  shape : ShapeHost.Guards c.shape (c.arrayLen + 1) k s
  arithmeticPre : LambdaPsiSweep.ArithmeticPre c k
    (arun k s c.shape.body)

theorem LambdaPsiSweep.body_defined_of_shapeHostInvariant
    (c : LambdaPsiSweep.Cfg) (k : Nat) (s : AState)
    (hw : ∀ j, s.regs j < M) (ha : ∀ j, s.arr j < M)
    (h : LambdaPsiSweep.ShapeHostInvariant c k s) :
    AllDefined (c.arrayLen + 1) k s (LambdaPsiSweep.body c) := by
  rw [LambdaPsiSweep.body_eq_shape_arithmetic, AllDefined_append]
  exact ⟨ShapeHost.body_defined_of_guards c.shape (c.arrayLen + 1) k s
      hw ha h.shape,
    LambdaPsiSweep.arithmeticBody_defined_of_pre c k _ h.arithmeticPre⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock

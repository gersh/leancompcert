import LeanCompCert.Ports.R2RuntimeTable
import LeanCompCert.Verified.ArrayFoldBridge

/-! # Source semantics of the compiled R2 composite-mark stage -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

def rootMarkWidth : Nat := 379
def rootMarkN (index : Nat) : Nat := index / rootMarkWidth + 2
def rootMarkD (index : Nat) : Nat := index % rootMarkWidth + 2
def rootMarkHit (index : Nat) : Nat :=
  if rootMarkD index * rootMarkD index ≤ rootMarkN index ∧
      rootMarkN index % rootMarkD index = 0 then 1 else 0

theorem rootMark_index_bounds {index : Nat}
    (hi : index < (runtimeRoot - 1) * rootMarkWidth) :
    index < M ∧ rootMarkN index ≤ runtimeRoot ∧
      2 ≤ rootMarkD index ∧ rootMarkD index ≤ runtimeDivCap := by
  have hw : 0 < rootMarkWidth := by decide
  have hq : index / rootMarkWidth < runtimeRoot - 1 :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hi)
  have hr := Nat.mod_lt index hw
  simp [rootMarkN, rootMarkD, runtimeRoot, runtimeDivCap, rootMarkWidth] at hq hr ⊢
  constructor
  · exact Nat.lt_trans hi (by decide)
  constructor <;> omega

theorem rootMarkBody_defined (c : R2Cfg) (index : Nat) (s : AState)
    (hArray : c.arrayLen < M)
    (hRoot : runtimeRoot < c.arrayLen)
    (hi : index < (r2RootMarkProgram c).loopCount) :
    AllDefined c.arrayLen index s (rootMarkBody c) := by
  have hb := rootMark_index_bounds (index := index) (by simpa [r2RootMarkProgram,
    rootMarkWidth, runtimeDivCap] using hi)
  have hiM : index % M = index := Nat.mod_eq_of_lt hb.1
  have hwM : (379 : Nat) % M = 379 := Nat.mod_eq_of_lt (by decide)
  have hnM : rootMarkN index % M = rootMarkN index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hb.2.1 (by decide))
  have hdM : rootMarkD index % M = rootMarkD index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hb.2.2.2 (by decide))
  have hnRawM : (index / 379 + 2) % M = index / 379 + 2 := by
    simpa [rootMarkN, rootMarkWidth] using hnM
  have hdRawM : (index % 379 + 2) % M = index % 379 + 2 := by
    simpa [rootMarkD, rootMarkWidth] using hdM
  have hd0 : rootMarkD index ≠ 0 := by omega
  have hdPos : 0 < rootMarkD index := by omega
  have hOneM : 1 % M = 1 := Nat.mod_eq_of_lt (by decide)
  have hPredM : (M - 1) % M = M - 1 := Nat.mod_eq_of_lt (by
    exact Nat.sub_lt (by decide) (by decide))
  have hCancelM : (1 % M + (M - 1) % M) % M = 0 := by
    rw [hOneM, hPredM]
    rw [show 1 + (M - 1) = M by omega]
    exact Nat.mod_self M
  have hremM : (rootMarkN index % rootMarkD index) % M =
      rootMarkN index % rootMarkD index := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_trans (Nat.mod_lt _ hdPos)
      (Nat.lt_of_le_of_lt hb.2.2.2 (by decide))
  have hddM : (rootMarkD index * rootMarkD index) % M =
      rootMarkD index * rootMarkD index := Nat.mod_eq_of_lt (by
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hb.2.2.2 hb.2.2.2) (by decide))
  have hsink : rootMarkSink c < c.arrayLen := by
    unfold rootMarkSink R2Cfg.arrayLen R2Cfg.resultBase R2Cfg.streamSink
      R2Cfg.streamBase R2Cfg.tableBase
    omega
  have hsinkM : rootMarkSink c % M = rootMarkSink c :=
    Nat.mod_eq_of_lt (Nat.lt_trans hsink hArray)
  have hncell : rootMarkN index < c.arrayLen := by
    exact Nat.lt_of_le_of_lt hb.2.1 hRoot
  let sd := arun index s rootMarkDecode
  have hDecode : AllDefined c.arrayLen index s rootMarkDecode := by
    simp [rootMarkDecode, AllDefined, ADefined, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, hiM, hwM, M_pos]
  have sd11 : sd.regs 11 = rootMarkN index := by
    simp [sd, rootMarkDecode, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, rootMarkN, rootMarkWidth,
      hiM, hwM, hnM, hnRawM]
  have sd13 : sd.regs 13 = rootMarkD index := by
    simp [sd, rootMarkDecode, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, rootMarkD, rootMarkWidth,
      hiM, hwM, hdM, hdRawM]
  let sw := arun index sd rootMarkWitness
  have hWitness : AllDefined c.arrayLen index sd rootMarkWitness := by
    simp [rootMarkWitness, AllDefined, ADefined, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, sd11, sd13, hd0, hdM]
  have sw15 : sw.regs 15 =
      (if rootMarkD index * rootMarkD index ≤ rootMarkN index then 1 else 0) := by
    simp [sw, rootMarkWitness, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, sd11, sd13, hddM, hnM]
  have sw17 : sw.regs 17 =
      (if rootMarkN index % rootMarkD index = 0 then 1 else 0) := by
    simp [sw, rootMarkWitness, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, sd11, sd13, hd0, hdM,
      hremM]
  have sw11 : sw.regs 11 = rootMarkN index := by
    simp [sw, rootMarkWitness, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, sd11]
  let st := arun index sw (rootMarkTarget c)
  have hTarget : AllDefined c.arrayLen index sw (rootMarkTarget c) := by
    simp [rootMarkTarget, AllDefined, ADefined, astep, sval, sdest,
      denoteOperand, denoteOp]
  have st18 : st.regs 18 = rootMarkHit index := by
    simp [st, rootMarkTarget, rootMarkHit, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, RegState.set, sw15, sw17]
    by_cases hsq : rootMarkD index * rootMarkD index ≤ rootMarkN index
    · by_cases hrem : rootMarkN index % rootMarkD index = 0
      · simp [hsq, hrem, hOneM]
      · simp [hsq, hrem]
    · simp [hsq]
  have st22 : st.regs 22 =
      if rootMarkHit index = 1 then rootMarkN index else rootMarkSink c := by
    simp [st, rootMarkTarget, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, sw15, sw17, sd11,
      rootMarkHit]
    by_cases hsq : rootMarkD index * rootMarkD index ≤ rootMarkN index
    · by_cases hrem : rootMarkN index % rootMarkD index = 0
      · simp only [hsq, hrem, if_pos]
        rw [sw11]
        simp [hOneM, hnM, Nat.add_mod, Nat.mul_mod]
        rw [hCancelM]
        simp [hnM]
      · simp [hsq, hrem, sw11, hnM, hsinkM, hOneM, hPredM,
          Nat.add_mod, Nat.mul_mod]
    · simp [hsq, sw11, hnM, hsinkM, hOneM, hPredM,
        Nat.add_mod, Nat.mul_mod]
  unfold rootMarkBody
  rw [show rootMarkDecode ++ rootMarkWitness ++ rootMarkTarget c ++
      [.store 22 18] =
      rootMarkDecode ++ (rootMarkWitness ++ (rootMarkTarget c ++
        [.store 22 18])) by
      simp [List.append_assoc]]
  rw [AllDefined_append]
  refine ⟨hDecode, ?_⟩
  rw [AllDefined_append]
  refine ⟨hWitness, ?_⟩
  rw [AllDefined_append]
  refine ⟨hTarget, ?_⟩
  simp only [AllDefined, ADefined]
  rw [st22]
  split
  · exact ⟨hncell, trivial⟩
  · exact ⟨hsink, trivial⟩

/-- The source-level result of the mark stage.  This is intentionally an
opaque symbolic fold: Lean proves that each compiled step implements it but
does not reduce the production-sized loop. -/
def rootMarkFold (c : R2Cfg) (arr : Nat → Nat) : AState :=
  (List.range (r2RootMarkProgram c).loopCount).foldl
    (fun s index => arun index s (rootMarkBody c))
    (initialAStateWithArray arr)

def rootMarkedState (c : R2Cfg) (arr : Nat → Nat) : AState :=
  arun 0 (rootMarkFold c arr) (r2RootMarkProgram c).epilogue

theorem rootMarkProgram_runFromArray (c : R2Cfg) (arr : Nat → Nat)
    (hArray : c.arrayLen < M) (hRoot : runtimeRoot < c.arrayLen) :
    (r2RootMarkProgram c).runFromArray arr = some (rootMarkedState c arr) := by
  apply AProgram.runFromArray_eq_foldl_mem
    (P := fun _ => True)
    (step := fun index s => arun index s (rootMarkBody c))
    (fin := fun s => arun 0 s (r2RootMarkProgram c).epilogue)
    (s₀ := initialAStateWithArray arr)
  · rfl
  · trivial
  · intro index s hi _
    apply denoteAInstrs_eq_arun
    exact rootMarkBody_defined c index s hArray hRoot hi
  · intros; trivial
  · intro s _
    apply denoteAInstrs_eq_arun
    simp [r2RootMarkProgram, AllDefined, ADefined]

theorem rootMarkProduction_runFromArray (arr : Nat → Nat) :
    (r2RootMarkProgram runtimeProductionCfg).runFromArray arr =
      some (rootMarkedState runtimeProductionCfg arr) := by
  apply rootMarkProgram_runFromArray
  · decide
  · decide

#print axioms rootMarkBody_defined
#print axioms rootMarkProgram_runFromArray
#print axioms rootMarkProduction_runFromArray

end LeanCompCert.Ports.R2SegSieve

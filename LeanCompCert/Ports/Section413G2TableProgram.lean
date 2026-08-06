import LeanCompCert.Ports.Section413G2FinalDenote
import LeanCompCert.Ports.Section413G2Sound

/-!
# A verified-code carrier for a complete Section 4.13 `g₂` table

The already verified `Section413G2Program` computes the fixed-point `g₂`
sweep but returns only its violation bit.  This extension appends four simple
instructions to each loop round: on a candidate-finalization round it stores
the new lower and upper `g₂` endpoints in two extra array planes.  Its
epilogue compares those planes with a supplied certificate table.

The arithmetic sweep itself is unchanged.  In particular the substantial
machine/transparent-model proof in `Section413G2FinalDenote` remains the
source of truth for every base instruction; this module proves only the two
extra stores, the literal-table comparisons, and their frame properties.
-/

namespace LeanCompCert.Ports.Section413G2TableProgram

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.Section413G2Program
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells (encodeZ)

def regCount : Nat := 272

def tableLo (c : Cfg) : Nat := 3 * (c.cap + 1)
def tableHi (c : Cfg) : Nat := 4 * (c.cap + 1)
def tableArrayLen (c : Cfg) : Nat := 5 * (c.cap + 1)

/-- Canonical signed cells decoded from intrinsically bounded 64-bit words. -/
def cellsOfWords (words : Array (UInt64 × UInt64)) : Array Cell :=
  words.map fun p =>
    ⟨LeanCompCert.Ports.Section413Cells.decodeZ p.1.toNat,
      LeanCompCert.Ports.Section413Cells.decodeZ p.2.toNat⟩

def rAddrLo : Nat := 256
def rAddrHi : Nat := 257
def rValLo : Nat := 258
def rValHi : Nat := 259
def rCheckAddr : Nat := 260
def rCheckVal : Nat := 261
def rBad : Nat := 262

/-- Store the new `g` cell on finalization rounds.  Inactive rounds write zero
to slot zero of the two extra planes, which is outside the certified range
`1 .. cap`. -/
def tableStorePrep (c : Cfg) : List AInstr :=
  [ .scalar (.binop rAddrLo .mul (.reg 35) (.reg 31))
  , .scalar (.binop rAddrLo .add (.reg rAddrLo) (.lit (tableLo c)))
  , .scalar (.binop rAddrLo .urem (.reg rAddrLo) (.lit (tableArrayLen c)))
  , .scalar (.binop rAddrHi .mul (.reg 35) (.reg 31))
  , .scalar (.binop rAddrHi .add (.reg rAddrHi) (.lit (tableHi c)))
  , .scalar (.binop rAddrHi .urem (.reg rAddrHi) (.lit (tableArrayLen c)))
  , .scalar (.binop rValLo .mul (.reg 35) (.reg 12))
  , .scalar (.binop rValHi .mul (.reg 35) (.reg 13)) ]

def tableStoreBody (c : Cfg) : List AInstr :=
  tableStorePrep c ++ [.store rAddrLo rValLo, .store rAddrHi rValHi]

def checkWord (address expected : Nat) : List AInstr :=
  [ .scalar (.mov rCheckAddr (.lit address))
  , .load rCheckVal rCheckAddr
  , .scalar (.binop rBad .ne (.reg rCheckVal) (.lit expected))
  , .scalar (.binop rViol .bor (.reg rViol) (.reg rBad)) ]

def checkCell (c : Cfg) (expected : Array Cell) (X : Nat) : List AInstr :=
  checkWord (tableLo c + X) (encodeZ expected[X]!.lo) ++
    checkWord (tableHi c + X) (encodeZ expected[X]!.hi)

def checkTable (c : Cfg) (expected : Array Cell) : List AInstr :=
  (List.range c.cap).flatMap (fun i => checkCell c expected (i + 1))

def tableProgram (c : Cfg) (expected : Array Cell) : AProgram := {
  regCount := regCount
  arrayLen := tableArrayLen c
  loopCount := c.loopCount
  init := c.init
  body := c.body ++ tableStoreBody c
  epilogue := checkTable c expected
  output := rViol
}

/-! ## Well-formedness and compiler bridge -/

theorem operand_wf_mono {a b : Nat} (hab : a ≤ b) (o : Operand)
    (h : o.WF a) : o.WF b := by
  cases o with
  | reg i => exact Nat.lt_of_lt_of_le h hab
  | lit | idx => trivial

theorem instr_wf_mono {a b : Nat} (hab : a ≤ b) (i : Instr)
    (h : i.WF a) : i.WF b := by
  cases i with
  | mov d s => exact ⟨Nat.lt_of_lt_of_le h.1 hab, operand_wf_mono hab s h.2⟩
  | binop d op l r =>
      exact ⟨Nat.lt_of_lt_of_le h.1 hab, operand_wf_mono hab l h.2.1,
        operand_wf_mono hab r h.2.2⟩

theorem ainstr_wf_mono {a b : Nat} (hab : a ≤ b) (i : AInstr)
    (h : i.WF a) : i.WF b := by
  cases i with
  | scalar s => exact instr_wf_mono hab s h
  | load d r => exact ⟨Nat.lt_of_lt_of_le h.1 hab, Nat.lt_of_lt_of_le h.2 hab⟩
  | store r s => exact ⟨Nat.lt_of_lt_of_le h.1 hab, Nat.lt_of_lt_of_le h.2 hab⟩

theorem base_init_wf (c : Cfg) : ∀ i ∈ c.init, i.WF regCount := by
  intro i hi
  exact ainstr_wf_mono (by decide :
    LeanCompCert.Ports.Section413G2Program.regCount ≤ regCount)
    i ((g2Program_wf c).2.1 i (by simpa [g2Program] using hi))

theorem base_body_wf (c : Cfg) : ∀ i ∈ c.body, i.WF regCount := by
  intro i hi
  exact ainstr_wf_mono (by decide :
    LeanCompCert.Ports.Section413G2Program.regCount ≤ regCount)
    i ((g2Program_wf c).2.2.1 i (by simpa [g2Program] using hi))

theorem tableStoreBody_wf (c : Cfg) : ∀ i ∈ tableStoreBody c, i.WF regCount := by
  intro i hi
  simp only [tableStoreBody, tableStorePrep, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [AInstr.WF, Instr.WF, Operand.WF, regCount, rAddrLo, rAddrHi,
        rValLo, rValHi]
  · rcases hi with rfl | rfl
    all_goals simp [AInstr.WF, regCount, rAddrLo, rAddrHi, rValLo, rValHi]

theorem checkWord_wf (address expected : Nat) :
    ∀ i ∈ checkWord address expected, i.WF regCount := by
  intro i hi
  simp only [checkWord, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [AInstr.WF, Instr.WF, Operand.WF, regCount, rCheckAddr,
      rCheckVal, rBad, rViol]

theorem checkCell_wf (c : Cfg) (expected : Array Cell) (X : Nat) :
    ∀ i ∈ checkCell c expected X, i.WF regCount := by
  intro i hi
  simp only [checkCell, List.mem_append] at hi
  exact hi.elim (checkWord_wf _ _ i) (checkWord_wf _ _ i)

theorem checkTable_wf (c : Cfg) (expected : Array Cell) :
    ∀ i ∈ checkTable c expected, i.WF regCount := by
  intro i hi
  simp only [checkTable, List.mem_flatMap] at hi
  obtain ⟨x, -, hx⟩ := hi
  exact checkCell_wf c expected (x + 1) i hx

theorem tableProgram_wf (c : Cfg) (expected : Array Cell) :
    (tableProgram c expected).WF := by
  refine ⟨show rViol < regCount by decide, base_init_wf c, ?_,
    checkTable_wf c expected⟩
  intro i hi
  simp only [tableProgram, List.mem_append] at hi
  exact hi.elim (base_body_wf c i) (tableStoreBody_wf c i)

theorem tableProgram_compiled (c : Cfg) (expected : Array Cell) (base : Int)
    (hBase : BaseOk (tableProgram c expected).arrayLen base)
    (n : Nat) (hDenote : (tableProgram c expected).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((tableProgram c expected).initialMCC base)
          (tableProgram c expected).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(tableProgram c expected).output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (tableProgram_wf c expected) base hBase n hDenote

/-! ## Raw denotation -/

open LeanCompCert.Verified.ArrayFoldBridge

abbrev DAdmissible := LeanCompCert.Ports.Section413G2Denote.Admissible

structure TableAdmissible (c : Cfg) : Prop where
  base : DAdmissible c
  tableLt : tableArrayLen c < M

theorem adefined_mono_len {a b k : Nat} (hab : a ≤ b) (s : AState)
    (i : AInstr) (h : ADefined a k s i) : ADefined b k s i := by
  cases i with
  | scalar instr =>
      cases instr <;> simpa [ADefined] using h
  | load d r => exact Nat.lt_of_lt_of_le h hab
  | store r v => exact Nat.lt_of_lt_of_le h hab

theorem allDefined_mono_len {a b k : Nat} (hab : a ≤ b) :
    ∀ (l : List AInstr) (s : AState),
      AllDefined a k s l → AllDefined b k s l := by
  intro l
  induction l with
  | nil => intro s h; trivial
  | cons i rest ih =>
      intro s h
      exact ⟨adefined_mono_len hab s i h.1, ih (astep k s i) h.2⟩

def WordInv (s : AState) : Prop :=
  (∀ j, s.regs j < M) ∧ ∀ i, s.arr i < M

theorem tableArrayLen_pos (c : Cfg) : 0 < tableArrayLen c := by
  simp [tableArrayLen]

theorem base_len_le_table_len (c : Cfg) : c.arrayLen ≤ tableArrayLen c := by
  simp [Cfg.arrayLen, tableArrayLen]
  omega

theorem tableStoreBody_defined (c : Cfg) (k : Nat) (s : AState) :
    TableAdmissible c → AllDefined (tableArrayLen c) k s (tableStoreBody c) := by
  intro hc
  have hp := tableArrayLen_pos c
  have hmod : tableArrayLen c % M = tableArrayLen c := Nat.mod_eq_of_lt hc.tableLt
  have hprep : (tableStorePrep c).all
      LeanCompCert.Ports.Section413G2Denote.alwaysDef = true := by
    simp [tableStorePrep, LeanCompCert.Ports.Section413G2Denote.alwaysDef,
      hmod, Nat.ne_of_gt hp]
  have hd := LeanCompCert.Ports.Section413G2Denote.allDefined_of_alwaysDef
    (tableArrayLen c) k (tableStorePrep c) s hprep
  rw [tableStoreBody, AllDefined_append]
  refine ⟨hd, ?_⟩
  let p := arun k s (tableStorePrep c)
  have hlo : p.regs rAddrLo < tableArrayLen c := by
    dsimp [p]
    simp [tableStorePrep, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hmod, Nat.ne_of_gt hp, rAddrLo, rAddrHi, rValLo, rValHi]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hp) hc.tableLt)]
    exact Nat.mod_lt _ hp
  have hhi : p.regs rAddrHi < tableArrayLen c := by
    dsimp [p]
    simp [tableStorePrep, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hmod, Nat.ne_of_gt hp, rAddrLo, rAddrHi, rValLo, rValHi]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hp) hc.tableLt)]
    exact Nat.mod_lt _ hp
  exact ⟨hlo, hhi, trivial⟩

theorem extended_body_defined (c : Cfg) (hc : TableAdmissible c) (idx : Nat)
    (hidx : idx < c.loopCount) (s : AState) (hs : WordInv s) :
    AllDefined (tableArrayLen c) idx s (c.body ++ tableStoreBody c) := by
  rw [AllDefined_append]
  have hb0 := LeanCompCert.Ports.Section413G2Denote.body_defined
    c hc.base idx hidx s hs.1 hs.2
  have hb := allDefined_mono_len (base_len_le_table_len c) c.body s hb0
  exact ⟨hb, tableStoreBody_defined c idx (arun idx s c.body) hc⟩

def flagStep (v : Nat) (bad : Prop) [Decidable bad] : Nat :=
  (v ||| bnat bad) % M

def checkCellValue (c : Cfg) (expected : Array Cell) (arr : Nat → Nat)
    (v X : Nat) : Nat :=
  flagStep (flagStep v
      (arr ((tableLo c + X) % M) ≠ encodeZ expected[X]!.lo % M))
    (arr ((tableHi c + X) % M) ≠ encodeZ expected[X]!.hi % M)

def checkTableValue (c : Cfg) (expected : Array Cell) (arr : Nat → Nat)
    (v : Nat) : Nat :=
  (List.range c.cap).foldl
    (fun v i => checkCellValue c expected arr v (i + 1)) v

theorem checkWord_run (address expected : Nat) (s : AState) :
    (arun 0 s (checkWord address expected)).regs rViol =
      flagStep (s.regs rViol) (s.arr (address % M) ≠ expected % M) := by
  simp [checkWord, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, RegState.set, flagStep,
    bnat, rCheckAddr, rCheckVal, rBad, rViol]

theorem checkWord_arr (address expected : Nat) (s : AState) :
    (arun 0 s (checkWord address expected)).arr = s.arr := by
  apply LeanCompCert.Ports.Section413G2Denote.arun_arr_frame
  intro i hi
  simp only [checkWord, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    rfl

theorem checkCell_run (c : Cfg) (expected : Array Cell) (X : Nat) (s : AState) :
    (arun 0 s (checkCell c expected X)).regs rViol =
      checkCellValue c expected s.arr (s.regs rViol) X := by
  rw [checkCell, arun_append, checkWord_run, checkWord_run,
    checkWord_arr]
  rfl

theorem checkCell_arr (c : Cfg) (expected : Array Cell) (X : Nat) (s : AState) :
    (arun 0 s (checkCell c expected X)).arr = s.arr := by
  rw [checkCell, arun_append, checkWord_arr, checkWord_arr]

theorem checkTable_run (c : Cfg) (expected : Array Cell) (s : AState) :
    (arun 0 s (checkTable c expected)).regs rViol =
      checkTableValue c expected s.arr (s.regs rViol) := by
  unfold checkTable checkTableValue
  induction (List.range c.cap) generalizing s with
  | nil => rfl
  | cons X xs ih =>
      rw [List.flatMap_cons, arun_append, ih, checkCell_arr, checkCell_run]
      rfl

theorem checkWord_defined {len address expected : Nat} (s : AState)
    (haddr : address < len) (hlen : len < M) :
    AllDefined len 0 s (checkWord address expected) := by
  have haddressM : address < M := Nat.lt_trans haddr hlen
  have haddressMod : address % M = address := Nat.mod_eq_of_lt haddressM
  simp [checkWord, AllDefined, ADefined, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, haddressMod, haddr, rCheckAddr, rCheckVal, rBad, rViol]

theorem checkCell_defined (c : Cfg) (expected : Array Cell) (X : Nat)
    (s : AState) (hc : TableAdmissible c) (hX : X ≤ c.cap) :
    AllDefined (tableArrayLen c) 0 s (checkCell c expected X) := by
  rw [checkCell, AllDefined_append]
  constructor
  · apply checkWord_defined s (hlen := hc.tableLt)
    simp [tableLo, tableArrayLen]
    omega
  · apply checkWord_defined _ (hlen := hc.tableLt)
    simp [tableHi, tableArrayLen]
    omega

theorem checkCells_defined (c : Cfg) (expected : Array Cell)
    (xs : List Nat) (s : AState) (hc : TableAdmissible c)
    (hxs : ∀ i ∈ xs, i < c.cap) :
    AllDefined (tableArrayLen c) 0 s
      (xs.flatMap (fun i => checkCell c expected (i + 1))) := by
  induction xs generalizing s with
  | nil => trivial
  | cons i rest ih =>
      rw [List.flatMap_cons, AllDefined_append]
      refine ⟨checkCell_defined c expected (i + 1) s hc (by
        have := hxs i (by simp)
        omega), ?_⟩
      exact ih (arun 0 s (checkCell c expected (i + 1)))
        (fun j hj => hxs j (by simp [hj]))

theorem checkTable_defined (c : Cfg) (expected : Array Cell) (s : AState)
    (hc : TableAdmissible c) :
    AllDefined (tableArrayLen c) 0 s (checkTable c expected) := by
  apply checkCells_defined c expected (List.range c.cap) s hc
  intro i hi
  simpa using (List.mem_range.mp hi)

def rawEntry (c : Cfg) : AState :=
  arun 0 initialAState c.init

def rawStep (c : Cfg) (idx : Nat) (s : AState) : AState :=
  arun idx s (c.body ++ tableStoreBody c)

def rawFinal (c : Cfg) : AState :=
  (List.range c.loopCount).foldl (fun s idx => rawStep c idx s) (rawEntry c)

def rawValue (c : Cfg) (expected : Array Cell) : Nat :=
  checkTableValue c expected (rawFinal c).arr ((rawFinal c).regs rViol)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem extended_body_wordInv (c : Cfg) (idx : Nat) (s : AState)
    (hs : WordInv s) : WordInv (rawStep c idx s) := by
  change WordInv (arun idx s (c.body ++ tableStoreBody c))
  exact LeanCompCert.Ports.Section413G2Denote.arun_lt idx
    (c.body ++ tableStoreBody c) s hs.1 hs.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
def rawLoop (c : Cfg) (expected : Array Cell) (hc : TableAdmissible c) :
    LeanCompCert.Verified.Algorithm.ArrayLoop AState where
  program := tableProgram c expected
  inv := WordInv
  step := rawStep c
  obs := id
  g := rawStep c
  out := fun s => checkTableValue c expected s.arr (s.regs rViol)
  entry := rawEntry c
  init_reaches := by
    apply denoteAInstrs_eq_arun
    have hi := (LeanCompCert.Ports.Section413G2Denote.init_reaches_tInit c
      (by simp [Cfg.arrayLen]; omega)).1
    exact allDefined_mono_len (base_len_le_table_len c) c.init initialAState hi
  inv_entry := by
    refine ⟨LeanCompCert.Ports.Section413G2Denote.arun_regs_lt
        0 c.init initialAState ?_ ?_,
      LeanCompCert.Ports.Section413G2Denote.arun_arr_lt
        0 c.init initialAState ?_ ?_⟩ <;>
      simp [initialAState, initialState, M]
  body_sim := by
    intro idx s hidx hs
    apply denoteAInstrs_eq_arun
    exact extended_body_defined c hc idx hidx s hs
  inv_step := by
    intro idx s hidx hs
    exact extended_body_wordInv c idx s hs
  obs_step := by
    intro index s hidx hs
    show id (rawStep c index s) = rawStep c index (id s)
    simp only [id_eq]
  epilogue_reads := by
    intro s hs
    rw [show (tableProgram c expected).epilogue = checkTable c expected from rfl]
    change Option.map (fun s' => s'.regs rViol)
      (denoteAInstrs (tableArrayLen c) 0 s (checkTable c expected)) = _
    rw [denoteAInstrs_eq_arun _ _ _ _ (checkTable_defined c expected s hc)]
    simp only [Option.map_some]
    exact congrArg some (checkTable_run c expected s)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem rawLoop_value (c : Cfg) (expected : Array Cell) (hc : TableAdmissible c) :
    (rawLoop c expected hc).value = rawValue c expected := by
  change checkTableValue c expected
      (List.foldl (fun acc index => rawStep c index acc) (rawEntry c)
        (List.range (tableProgram c expected).loopCount)).arr
      ((List.foldl (fun acc index => rawStep c index acc) (rawEntry c)
        (List.range (tableProgram c expected).loopCount)).regs rViol) = rawValue c expected
  rw [show (tableProgram c expected).loopCount = c.loopCount from rfl]
  rfl

theorem tableProgram_denote (c : Cfg) (expected : Array Cell)
    (hc : TableAdmissible c) :
    (tableProgram c expected).denote = some (rawValue c expected) :=
  (rawLoop c expected hc).denote_eq (rawLoop_value c expected hc)

end LeanCompCert.Ports.Section413G2TableProgram

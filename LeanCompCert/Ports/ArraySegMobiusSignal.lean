import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Ports.MobiusResidueModel
import LeanCompCert.Ports.MobiusResidueWindow
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Isolated signal decoder of the segmented Möbius sieve

The production segmented loop is long because it marks cells, advances a
prime cursor, decodes a cell, clears it, and bootstraps the prime table in one
branchless block.  The residue only consumes four registers.  This file
extracts, rather than retranscribes, the twenty-instruction slice that writes
those registers and proves its exact ordinary-arithmetic meaning.

The remaining number-theoretic refinement can now target the two marked cells
`prod` and `flag`: once they satisfy `CellRepresents`, the emitted registers
are exactly `muSig`.  No compiler or instruction semantics remain in that
obligation.
-/

namespace LeanCompCert.Ports.ArraySegMobiusSignal

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.MobiusResidueRealisation

/-- Instructions 66 through 85 of `coreBody`, obtained by list slicing. -/
def signalBlock (c : Cfg) : List AInstr :=
  (c.coreBody.drop 66).take 20

def preSignal (c : Cfg) : List AInstr := c.coreBody.take 66

def postSignal (c : Cfg) : List AInstr := c.coreBody.drop 86

def selectorBlock (c : Cfg) : List AInstr := c.coreBody.take 7

def markPrefix (c : Cfg) : List AInstr := (preSignal c).drop 7

/-- The store-free prefix of the marking code. -/
def markBeforeProd (c : Cfg) : List AInstr := (markPrefix c).take 23

/-- The store-free instructions between the product and flag stores. -/
def markBetweenStores (c : Cfg) : List AInstr :=
  ((markPrefix c).drop 24).take 8

/-- The store-free remainder after the flag store. -/
def markAfterFlag (c : Cfg) : List AInstr := (markPrefix c).drop 33

def signalInput (c : Cfg) (idx : Nat) (s : AState) : AState :=
  arun idx s (preSignal c)

theorem signalBlock_length (c : Cfg) : (signalBlock c).length = 20 := by
  rfl

theorem coreBody_eq_signalSlices (c : Cfg) :
    c.coreBody = preSignal c ++ signalBlock c ++ postSignal c := by
  rfl

theorem preSignal_eq_selector_mark (c : Cfg) :
    preSignal c = selectorBlock c ++ markPrefix c := by
  rfl

theorem markPrefix_eq_storeSlices (c : Cfg) :
    markPrefix c =
      markBeforeProd c ++ [.store 25 30] ++
      markBetweenStores c ++ [.store 26 38] ++ markAfterFlag c := by
  rfl

/-- Register-frame predicate for an array instruction. -/
def avoidsReg (r : Nat) : AInstr → Bool
  | .scalar (.mov d _) => d != r
  | .scalar (.binop d _ _ _) => d != r
  | .load d _ => d != r
  | .store _ _ => true

theorem arun_reg_frame (k r : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all (avoidsReg r) = true → (arun k s l).regs r = s.regs r := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr =>
          cases instr with
          | mov d src =>
              simp only [avoidsReg, bne_iff_ne] at h
              simp [astep, LeanCompCert.Verified.InstrBlock.sdest,
                LeanCompCert.Verified.InstrBlock.sval,
                AState.writeReg, Ne.symm h.1]
          | binop d op lhs rhs =>
              simp only [avoidsReg, bne_iff_ne] at h
              simp [astep, LeanCompCert.Verified.InstrBlock.sdest,
                LeanCompCert.Verified.InstrBlock.sval,
                AState.writeReg, Ne.symm h.1]
      | load d a =>
          simp only [avoidsReg, bne_iff_ne] at h
          simp [astep, AState.writeReg, Ne.symm h.1]
      | store a v => rfl

/-- Store-free instruction blocks preserve the entire array. -/
def avoidsStore : AInstr → Bool
  | .store _ _ => false
  | _ => true

theorem arun_arr_frame (k : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all avoidsStore = true → (arun k s l).arr = s.arr := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => exact AState.writeReg_arr _ _ _
      | load d a => exact AState.writeReg_arr _ _ _
      | store a v => simp [avoidsStore] at h

/-- With marking disabled, both store addresses computed by the prefix are
the two dedicated sink cells. -/
theorem markBeforeProd_main_addresses (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 0)
    (hA : c.arrayLen < M) :
    (arun idx s (markBeforeProd c)).regs 25 = c.sinkProd ∧
      (arun idx s (markBeforeProd c)).regs 26 = c.sinkProd + c.segLen := by
  have hL : c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase] at hA
    omega
  have h2L : c.sinkProd < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase, Cfg.sinkProd] at hA ⊢
    omega
  have h3L : c.sinkProd + c.segLen < M := by
    simp only [Cfg.arrayLen, Cfg.resultBase, Cfg.sinkProd] at hA ⊢
    omega
  have hLM : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hL
  have h2LM : c.sinkProd % M = c.sinkProd := Nat.mod_eq_of_lt h2L
  have h3LM : (c.sinkProd + c.segLen) % M = c.sinkProd + c.segLen :=
    Nat.mod_eq_of_lt h3L
  set_option maxRecDepth 10000 in
    simp [markBeforeProd, markPrefix, preSignal, Cfg.coreBody, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rR, rW, rP, rJ, rPi, rLimit, hgate, hLM, h2LM, h3LM]

/-- On an accumulation iteration, the marking prefix redirects both stores
to its sinks and therefore preserves every product/flag cell in the live
window. -/
theorem arun_markPrefix_main_cells (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 0)
    (hA : c.arrayLen < M) (i : Nat) (hi : i < c.segLen) :
    (arun idx s (markPrefix c)).arr i = s.arr i ∧
      (arun idx s (markPrefix c)).arr (i + c.segLen) =
        s.arr (i + c.segLen) := by
  let s0 := arun idx s (markBeforeProd c)
  let s1 := astep idx s0 (.store 25 30)
  let s2 := arun idx s1 (markBetweenStores c)
  let s3 := astep idx s2 (.store 26 38)
  have haddrs := markBeforeProd_main_addresses c idx s hgate hA
  have h25 : s0.regs 25 = c.sinkProd := by exact haddrs.1
  have h26 : s0.regs 26 = c.sinkProd + c.segLen := by exact haddrs.2
  have hs0arr : s0.arr = s.arr :=
    arun_arr_frame idx (markBeforeProd c) s (by rfl)
  have hs2arr : s2.arr = s1.arr :=
    arun_arr_frame idx (markBetweenStores c) s1 (by rfl)
  have hs2r26 : s2.regs 26 = c.sinkProd + c.segLen := by
    rw [arun_reg_frame idx 26 (markBetweenStores c) s1 (by rfl)]
    exact h26
  have hdecomp : arun idx s (markPrefix c) =
      arun idx s3 (markAfterFlag c) := by
    rw [markPrefix_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append]
    rfl
  have preserve (x : Nat) (hprod : x ≠ c.sinkProd)
      (hflag : x ≠ c.sinkProd + c.segLen) :
      (arun idx s (markPrefix c)).arr x = s.arr x := by
    rw [hdecomp]
    rw [congrFun (arun_arr_frame idx (markAfterFlag c) s3 (by rfl)) x]
    change s3.arr x = s.arr x
    rw [show s3.arr x = s2.arr x by
      simp [s3, astep, AState.writeArr, hs2r26, hflag]]
    rw [congrFun hs2arr x]
    change s1.arr x = s.arr x
    rw [show s1.arr x = s0.arr x by
      simp [s1, astep, AState.writeArr, h25, hprod]]
    exact congrFun hs0arr x
  constructor
  · apply preserve
    · simp only [Cfg.sinkProd]; omega
    · simp only [Cfg.sinkProd]; omega
  · apply preserve
    · simp only [Cfg.sinkProd]; omega
    · simp only [Cfg.sinkProd]; omega

/-- Generic disabled-mark frame theorem.  This is the table-preservation form
of `arun_markPrefix_main_cells`: only the two dedicated sink cells can change
while the main accumulation gate is active. -/
theorem arun_markPrefix_main_frame (c : Cfg) (idx : Nat) (s : AState)
    (hgate : s.regs 8 = 0) (hA : c.arrayLen < M) (x : Nat)
    (hprod : x ≠ c.sinkProd)
    (hflag : x ≠ c.sinkProd + c.segLen) :
    (arun idx s (markPrefix c)).arr x = s.arr x := by
  let s0 := arun idx s (markBeforeProd c)
  let s1 := astep idx s0 (.store 25 30)
  let s2 := arun idx s1 (markBetweenStores c)
  let s3 := astep idx s2 (.store 26 38)
  have haddrs := markBeforeProd_main_addresses c idx s hgate hA
  have h25 : s0.regs 25 = c.sinkProd := haddrs.1
  have h26 : s0.regs 26 = c.sinkProd + c.segLen := haddrs.2
  have hs0arr : s0.arr = s.arr :=
    arun_arr_frame idx (markBeforeProd c) s (by rfl)
  have hs2arr : s2.arr = s1.arr :=
    arun_arr_frame idx (markBetweenStores c) s1 (by rfl)
  have hs2r26 : s2.regs 26 = c.sinkProd + c.segLen := by
    rw [arun_reg_frame idx 26 (markBetweenStores c) s1 (by rfl)]
    exact h26
  have hdecomp : arun idx s (markPrefix c) =
      arun idx s3 (markAfterFlag c) := by
    rw [markPrefix_eq_storeSlices, arun_append, arun_append, arun_append,
      arun_append]
    rfl
  rw [hdecomp]
  rw [congrFun (arun_arr_frame idx (markAfterFlag c) s3 (by rfl)) x]
  change s3.arr x = s.arr x
  rw [show s3.arr x = s2.arr x by
    simp [s3, astep, AState.writeArr, hs2r26, hflag]]
  rw [congrFun hs2arr x]
  change s1.arr x = s.arr x
  rw [show s1.arr x = s0.arr x by
    simp [s1, astep, AState.writeArr, h25, hprod]]
  exact congrFun hs0arr x

/-- On a main-phase iteration the seven selector instructions set both the
accumulation and main gates to one. -/
theorem selectorBlock_main (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hRoot : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M) :
    (arun idx s (selectorBlock c)).regs 9 = 1 ∧
      (arun idx s (selectorBlock c)).regs 133 = 1 := by
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hRmod : s.regs rR % M = s.regs rR := Nat.mod_eq_of_lt hRM
  have hImod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hRootmod : c.rootSpan % M = c.rootSpan := Nat.mod_eq_of_lt hrootM
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hT' : ¬ s.regs 5 < c.markSteps := by
    have : c.markSteps ≤ s.regs 5 := by simpa [rR] using hT
    omega
  have hRoot' : ¬ idx < c.rootSpan := by omega
  have hOne : (1 + M) % M = 1 := by decide
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rLimit, hTmod, hImod, hRootmod, h1mod, hT', hRoot', hOne]

/-- The final selector instruction defines the main gate as `inAcc -
inAccRoot`, independently of the active phase. -/
theorem selectorBlock_gate_eq (c : Cfg) (idx : Nat) (s : AState) :
    let q := arun idx s (selectorBlock c)
    q.regs 133 = (q.regs 9 + (M - q.regs 132)) % M := by
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rR, rLimit]

/-- The marking prefix frames all three selector outputs, so the same gate
equation holds at decoder entry. -/
theorem signalInput_gate_eq (c : Cfg) (idx : Nat) (s : AState) :
    let q := signalInput c idx s
    q.regs 133 = (q.regs 9 + (M - q.regs 132)) % M := by
  let q := arun idx s (selectorBlock c)
  have h := selectorBlock_gate_eq c idx s
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  dsimp only
  rw [arun_reg_frame idx 133 (markPrefix c) q (by rfl),
    arun_reg_frame idx 9 (markPrefix c) q (by rfl),
    arun_reg_frame idx 132 (markPrefix c) q (by rfl)]
  exact h

/-- On an accumulation iteration the selector disables the marking stores. -/
theorem selectorBlock_main_markGate (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hTM : c.markSteps < M) :
    (arun idx s (selectorBlock c)).regs 8 = 0 := by
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hT' : ¬ s.regs 5 < c.markSteps := by
    have : c.markSteps ≤ s.regs 5 := by simpa [rR] using hT
    omega
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rR, rLimit, hTmod, hT']

/-- The mark prefix does not change either selector output or the window
coordinates used by the decoder. -/
theorem signalInput_main_controls (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hRoot : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M) :
    (signalInput c idx s).regs rR = s.regs rR ∧
      (signalInput c idx s).regs rW = s.regs rW ∧
      (signalInput c idx s).regs 9 = 1 ∧
      (signalInput c idx s).regs 133 = 1 := by
  have hsel := selectorBlock_main c idx s hT hRoot hRM hTM hidxM hrootM
  have hR := arun_reg_frame idx rR (preSignal c) s (by rfl)
  have hW := arun_reg_frame idx rW (preSignal c) s (by rfl)
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  refine ⟨hR, hW, ?_, ?_⟩
  · rw [arun_reg_frame idx 9 (markPrefix c) _ (by rfl)]
    exact hsel.1
  · rw [arun_reg_frame idx 133 (markPrefix c) _ (by rfl)]
    exact hsel.2

/-- The two live cells read by the decoder are already present at loop entry;
the disabled marking stage only touches its sinks. -/
theorem signalInput_main_cells (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hTM : c.markSteps < M)
    (hA : c.arrayLen < M) (i : Nat) (hi : i < c.segLen) :
    (signalInput c idx s).arr i = s.arr i ∧
      (signalInput c idx s).arr (i + c.segLen) =
        s.arr (i + c.segLen) := by
  let q := arun idx s (selectorBlock c)
  have hgate : q.regs 8 = 0 :=
    selectorBlock_main_markGate c idx s hT hTM
  have hqarr : q.arr = s.arr :=
    arun_arr_frame idx (selectorBlock c) s (by rfl)
  have hp := arun_markPrefix_main_cells c idx q hgate hA i hi
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  constructor
  · rw [hp.1]; exact congrFun hqarr i
  · rw [hp.2]; exact congrFun hqarr (i + c.segLen)

/-- The complete selector/disabled-mark prefix frames every nonsink cell in
the main accumulation phase. -/
theorem signalInput_main_frame (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hTM : c.markSteps < M) (hA : c.arrayLen < M) (x : Nat)
    (hprod : x ≠ c.sinkProd)
    (hflag : x ≠ c.sinkProd + c.segLen) :
    (signalInput c idx s).arr x = s.arr x := by
  let q := arun idx s (selectorBlock c)
  have hgate : q.regs 8 = 0 :=
    selectorBlock_main_markGate c idx s hT hTM
  have hqarr : q.arr = s.arr :=
    arun_arr_frame idx (selectorBlock c) s (by rfl)
  have hp := arun_markPrefix_main_frame c idx q hgate hA x hprod hflag
  rw [signalInput, preSignal_eq_selector_mark, arun_append]
  exact hp.trans (congrFun hqarr x)

/-- The tail clears cells, bootstraps primes, and advances cursors, but does
not overwrite any of the four registers observed by a Möbius residue. -/
theorem readSig_arun_postSignal (c : Cfg) (idx : Nat) (s : AState) :
    readSig (arun idx s (postSignal c)) = readSig s := by
  have h65 := arun_reg_frame idx 65 (postSignal c) s (by rfl)
  have h79 := arun_reg_frame idx 79 (postSignal c) s (by rfl)
  have h80 := arun_reg_frame idx 80 (postSignal c) s (by rfl)
  have h133 := arun_reg_frame idx 133 (postSignal c) s (by rfl)
  simp only [readSig, h65, h79, h80, h133]

/-- Transparent decoding of the product/parity cells read by the extracted
block.  The `% M` operations are exactly the word reductions performed by the
machine instructions; they are deliberately visible to the subsequent pure
cell-refinement proof. -/
def decodeCell (n prod flag : Nat) : Sig :=
  let prod1 := (prod + if prod = 0 then 1 else 0) % M
  let sq := ((flag >>> 1) % M &&& 1) % M
  let parity := ((flag &&& 1) % M ^^^
    (if prod1 = n then 0 else 1)) % M
  let squarefree := (1 + (M - sq)) % M
  ⟨n,
    (squarefree * ((1 + (M - parity)) % M)) % M,
    (squarefree * parity) % M,
    1⟩

/-- Apply the selector gate to a decoded signal exactly as the last two
instructions of `signalBlock` do. -/
def gateSig (gate : Nat) (g : Sig) : Sig :=
  ⟨g.n, gate * g.pos % M, gate * g.neg % M, gate⟩

/-- Exact word-level cell selected by the decoder before ordinary-arithmetic
range hypotheses simplify its coordinates. -/
def machineDecodeCell (c : Cfg) (s : AState) : Sig :=
  let i := (s.regs rR + (M - c.markSteps % M)) % M
  let gatedI := s.regs 9 * i % M
  decodeCell ((gatedI + s.regs rW) % M)
    (s.arr gatedI) (s.arr ((gatedI + c.segLen) % M))

/-- The pure cell property the segmented-sieve mathematics must establish. -/
def CellRepresents (mu : Nat → Int) (n prod flag : Nat) : Prop :=
  decodeCell n prod flag = muSig mu n

/-- The extracted block's two loads are in bounds in the production two-bank
layout.  Scalar instructions in this slice contain no partial division or
remainder operations, so these are its complete definedness conditions. -/
theorem signalBlock_defined (arrayLen : Nat) (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hmain : s.regs 9 = 1)
    (_hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (harray : c.segLen + c.segLen ≤ arrayLen) :
    AllDefined arrayLen idx s (signalBlock c) := by
  have hsub :
      (s.regs rR + (M - c.markSteps)) % M = s.regs rR - c.markSteps := by
    have heq : s.regs rR + (M - c.markSteps) =
        M + (s.regs rR - c.markSteps) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have hiM : s.regs rR - c.markSteps < M := by omega
  have hiLM : s.regs rR - c.markSteps + c.segLen < M := by omega
  have hiA : s.regs rR - c.markSteps < arrayLen := by omega
  have hiLA : s.regs rR - c.markSteps + c.segLen < arrayLen := by omega
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hsub' :
      (s.regs 5 + (M - c.markSteps)) % M = s.regs 5 - c.markSteps := by
    simpa [rR] using hsub
  have hiM' : s.regs 5 - c.markSteps < M := by simpa [rR] using hiM
  have hiLM' : s.regs 5 - c.markSteps + c.segLen < M := by
    simpa [rR] using hiLM
  have hiA' : s.regs 5 - c.markSteps < arrayLen := by simpa [rR] using hiA
  have hiLA' : s.regs 5 - c.markSteps + c.segLen < arrayLen := by
    simpa [rR] using hiLA
  set_option maxRecDepth 10000 in
  simp [signalBlock, Cfg.coreBody, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg,
    rR, rW, hmain, hTmod, hsub', Nat.mod_eq_of_lt hiM',
    Nat.mod_eq_of_lt hiLM', hiA', hiLA']

/-- Partial array-machine denotation of the extracted decoder block. -/
theorem denote_signalBlock (arrayLen : Nat) (c : Cfg) (idx : Nat) (s : AState)
    (hdef : AllDefined arrayLen idx s (signalBlock c)) :
    denoteAInstrs arrayLen idx s (signalBlock c) =
      some (arun idx s (signalBlock c)) :=
  denoteAInstrs_eq_arun arrayLen idx (signalBlock c) s hdef

/-- Exact meaning of the extracted twenty instructions with an arbitrary
selector gate. -/
theorem readSig_arun_signalBlock_gated (c : Cfg) (idx : Nat) (s : AState)
    : readSig (arun idx s (signalBlock c)) =
      gateSig (s.regs 133) (machineDecodeCell c s) := by
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hmod2 (n : Nat) : n % 2 % M = n % 2 := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  set_option maxRecDepth 10000 in
  simp [signalBlock, Cfg.coreBody, machineDecodeCell, decodeCell, gateSig,
    readSig, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rR, rW, h1mod, hmod2]

/-- Whole-core form of the exact gated decoder theorem. -/
theorem readSig_arun_coreBody_gated (c : Cfg) (idx : Nat) (s : AState) :
    readSig (arun idx s c.coreBody) =
      gateSig ((signalInput c idx s).regs 133)
        (machineDecodeCell c (signalInput c idx s)) := by
  rw [coreBody_eq_signalSlices, arun_append, arun_append,
    readSig_arun_postSignal]
  simpa [signalInput] using
    readSig_arun_signalBlock_gated c idx (signalInput c idx s)

/-- Main-phase specialization of the gated decoder theorem. -/
theorem readSig_arun_signalBlock (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hgate : s.regs 133 = 1)
    (hmain : s.regs 9 = 1)
    (_hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M) :
    readSig (arun idx s (signalBlock c)) =
      decodeCell (s.regs rW + (s.regs rR - c.markSteps))
        (s.arr (s.regs rR - c.markSteps))
        (s.arr (s.regs rR - c.markSteps + c.segLen)) := by
  have hsub :
      (s.regs rR + (M - c.markSteps)) % M =
        s.regs rR - c.markSteps := by
    have heq : s.regs rR + (M - c.markSteps) =
        M + (s.regs rR - c.markSteps) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt]
    omega
  have hiM : s.regs rR - c.markSteps < M := by omega
  have hiLM : s.regs rR - c.markSteps + c.segLen < M := by omega
  have hTmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hTM
  have hsub' :
      (s.regs 5 + (M - c.markSteps)) % M =
        s.regs 5 - c.markSteps := by
    simpa [rR] using hsub
  have hiM' : s.regs 5 - c.markSteps < M := by simpa [rR] using hiM
  have hiLM' : s.regs 5 - c.markSteps + c.segLen < M := by
    simpa [rR] using hiLM
  have hWM' : s.regs 6 + (s.regs 5 - c.markSteps) < M := by
    simpa [rR, rW] using hWM
  have hni :
      (s.regs 5 - c.markSteps + s.regs 6) % M =
        s.regs 6 + (s.regs 5 - c.markSteps) := by
    rw [Nat.add_comm, Nat.mod_eq_of_lt hWM']
  have hmod2 (n : Nat) : n % 2 % M = n % 2 := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [readSig_arun_signalBlock_gated]
  simp [machineDecodeCell, gateSig, decodeCell, rR, rW, hTmod, hsub',
    Nat.mod_eq_of_lt hiM', Nat.mod_eq_of_lt hiLM', hni, hmain, hgate,
    hmod2]
  constructor <;> rfl

/-- Once the two cells have their mathematical Möbius meaning, the extracted
machine block emits the canonical signal consumed by every verified residue. -/
theorem readSig_eq_muSig_of_cell (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hgate : s.regs 133 = 1)
    (hmain : s.regs 9 = 1)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M)
    (hcell : CellRepresents mu
      (s.regs rW + (s.regs rR - c.markSteps))
      (s.arr (s.regs rR - c.markSteps))
      (s.arr (s.regs rR - c.markSteps + c.segLen))) :
    readSig (arun idx s (signalBlock c)) =
      muSig mu (s.regs rW + (s.regs rR - c.markSteps)) := by
  rw [readSig_arun_signalBlock c idx s hT hi hgate hmain hRM hTM h2LM hWM]
  exact hcell

/-- End-to-end partial denotation of the extracted block, including both load
bounds and its exact observable result. -/
theorem denote_signalBlock_readSig (arrayLen : Nat) (c : Cfg)
    (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hgate : s.regs 133 = 1)
    (hmain : s.regs 9 = 1)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (harray : c.segLen + c.segLen ≤ arrayLen)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M) :
    (denoteAInstrs arrayLen idx s (signalBlock c)).map readSig =
      some (decodeCell (s.regs rW + (s.regs rR - c.markSteps))
        (s.arr (s.regs rR - c.markSteps))
        (s.arr (s.regs rR - c.markSteps + c.segLen))) := by
  rw [denote_signalBlock arrayLen c idx s
    (signalBlock_defined arrayLen c idx s hT hi hmain hRM hTM h2LM harray)]
  simp only [Option.map_some]
  rw [readSig_arun_signalBlock c idx s hT hi hgate hmain hRM hTM h2LM hWM]

/-- Observable meaning of the complete 111-instruction core, factored through
the state immediately before its decoder slice.  The sole remaining
algorithmic obligation is to establish the hypotheses (and ultimately
`CellRepresents`) for `signalInput`. -/
theorem readSig_arun_coreBody (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ (signalInput c idx s).regs rR)
    (hi : (signalInput c idx s).regs rR - c.markSteps < c.segLen)
    (hgate : (signalInput c idx s).regs 133 = 1)
    (hmain : (signalInput c idx s).regs 9 = 1)
    (hRM : (signalInput c idx s).regs rR < M)
    (hTM : c.markSteps < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : (signalInput c idx s).regs rW +
      ((signalInput c idx s).regs rR - c.markSteps) < M) :
    readSig (arun idx s c.coreBody) =
      decodeCell
        ((signalInput c idx s).regs rW +
          ((signalInput c idx s).regs rR - c.markSteps))
        ((signalInput c idx s).arr
          ((signalInput c idx s).regs rR - c.markSteps))
        ((signalInput c idx s).arr
          ((signalInput c idx s).regs rR - c.markSteps + c.segLen)) := by
  rw [coreBody_eq_signalSlices, arun_append, arun_append,
    readSig_arun_postSignal]
  exact readSig_arun_signalBlock c idx (signalInput c idx s)
    hT hi hgate hmain hRM hTM h2LM hWM

/-- Main-phase form of the whole-core theorem.  Selector and coordinate
premises are discharged from the input state; only the marked array in
`signalInput` remains in the result. -/
theorem readSig_arun_coreBody_main (c : Cfg) (idx : Nat) (s : AState)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M) :
    readSig (arun idx s c.coreBody) =
      decodeCell (s.regs rW + (s.regs rR - c.markSteps))
        ((signalInput c idx s).arr (s.regs rR - c.markSteps))
        ((signalInput c idx s).arr
          (s.regs rR - c.markSteps + c.segLen)) := by
  have hc := signalInput_main_controls c idx s hT hRoot hRM hTM hidxM hrootM
  have hT' : c.markSteps ≤ (signalInput c idx s).regs rR := by
    rw [hc.1]; exact hT
  have hi' : (signalInput c idx s).regs rR - c.markSteps < c.segLen := by
    rw [hc.1]; exact hi
  have hRM' : (signalInput c idx s).regs rR < M := by
    rw [hc.1]; exact hRM
  have hWM' : (signalInput c idx s).regs rW +
      ((signalInput c idx s).regs rR - c.markSteps) < M := by
    rw [hc.1, hc.2.1]; exact hWM
  rw [readSig_arun_coreBody c idx s hT' hi' hc.2.2.2 hc.2.2.1
    hRM' hTM h2LM hWM', hc.1, hc.2.1]

/-- The production core emits the canonical Möbius signal once its two
marked cells satisfy the now-pure `CellRepresents` invariant. -/
theorem readSig_arun_coreBody_eq_muSig (c : Cfg) (idx : Nat) (s : AState)
    (mu : Nat → Int)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M)
    (hcell : CellRepresents mu
      (s.regs rW + (s.regs rR - c.markSteps))
      ((signalInput c idx s).arr (s.regs rR - c.markSteps))
      ((signalInput c idx s).arr
        (s.regs rR - c.markSteps + c.segLen))) :
    readSig (arun idx s c.coreBody) =
      muSig mu (s.regs rW + (s.regs rR - c.markSteps)) := by
  rw [readSig_arun_coreBody_main c idx s hT hi hRoot hRM hTM hidxM
    hrootM h2LM hWM]
  exact hcell

/-- Loop-entry form of the production correctness theorem.  The internal
marking prefix is eliminated: the only remaining sieve obligation is the
`CellRepresents` invariant carried into the accumulation iteration. -/
theorem readSig_arun_coreBody_eq_muSig_of_input_cell
    (c : Cfg) (idx : Nat) (s : AState) (mu : Nat → Int)
    (hT : c.markSteps ≤ s.regs rR)
    (hi : s.regs rR - c.markSteps < c.segLen)
    (hRoot : c.rootSpan ≤ idx)
    (hRM : s.regs rR < M)
    (hTM : c.markSteps < M)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M)
    (h2LM : c.segLen + c.segLen < M)
    (hWM : s.regs rW + (s.regs rR - c.markSteps) < M)
    (hA : c.arrayLen < M)
    (hcell : CellRepresents mu
      (s.regs rW + (s.regs rR - c.markSteps))
      (s.arr (s.regs rR - c.markSteps))
      (s.arr (s.regs rR - c.markSteps + c.segLen))) :
    readSig (arun idx s c.coreBody) =
      muSig mu (s.regs rW + (s.regs rR - c.markSteps)) := by
  apply readSig_arun_coreBody_eq_muSig c idx s mu hT hi hRoot hRM hTM
    hidxM hrootM h2LM hWM
  have hc := signalInput_main_cells c idx s hT hTM hA
    (s.regs rR - c.markSteps) hi
  unfold CellRepresents at hcell ⊢
  rw [hc.1, hc.2]
  exact hcell

end LeanCompCert.Ports.ArraySegMobiusSignal

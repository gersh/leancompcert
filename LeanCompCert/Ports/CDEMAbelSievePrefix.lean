import LeanCompCert.Ports.CDEMAbelSieve

/-! # Pure prefix model for CDEM resident Möbius rows -/

namespace LeanCompCert.Ports.CDEMAbelSievePrefix

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelSieve

/-- Exact word-level code emitted after one candidate has traversed the
resident prime list. -/
def sieveCodeOf (m par sqf : Nat) : Nat :=
  let large := if 1 < m then 1 else 0
  let sign := (par ^^^ large) % M
  (((sign + 1) % M) * sqf) % M

def sieveCodeBlock : List AInstr :=
  [ .scalar (.binop 61 .gt (.reg rM) (.lit 1))
  , .scalar (.binop 62 .bxor (.reg rPar) (.reg 61))
  , .scalar (.binop 63 .add (.reg 62) (.lit 1))
  , .scalar (.binop 63 .mul (.reg 63) (.reg rSqf)) ]

theorem sieveCodeBlock_run (idx : Nat) (st : AState) :
    (arun idx st sieveCodeBlock).regs 63 =
      sieveCodeOf (st.regs rM) (st.regs rPar) (st.regs rSqf) := by
  have h1M : (1 : Nat) % M = 1 := by decide
  simp [sieveCodeBlock, sieveCodeOf, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
    rM, rPar, rSqf, h1M]
  rfl

theorem sieveBody_code_split (c : Cfg) :
    c.sieveBody.take 29 = c.sieveBody.take 25 ++ sieveCodeBlock := by
  simp [Cfg.sieveBody, sieveCodeBlock, muxBody]

theorem sieveBody_prefix_code (c : Cfg) (idx : Nat) (st : AState) :
    (arun idx st (c.sieveBody.take 29)).regs 63 =
      let pre := arun idx st (c.sieveBody.take 25)
      sieveCodeOf (pre.regs rM) (pre.regs rPar) (pre.regs rSqf) := by
  rw [sieveBody_code_split, arun_append]
  exact sieveCodeBlock_run idx _

structure SieveFactorState where
  m : Nat
  par : Nat
  sqf : Nat

def sieveFactorHead : List AInstr :=
  [ .scalar (.binop 54 .urem (.reg rM) (.reg 53))
  , .scalar (.binop 55 .eq (.reg 54) (.lit 0))
  , .scalar (.binop 55 .mul (.reg 55) (.reg 40))
  , .scalar (.binop 56 .udiv (.reg rM) (.reg 53)) ]

def sieveFactorMux : List AInstr := muxBody rM 55 56 rM 57

def sieveFactorTail : List AInstr :=
  [ .scalar (.binop rPar .bxor (.reg rPar) (.reg 55))
  , .scalar (.binop 58 .urem (.reg rM) (.reg 53))
  , .scalar (.binop 59 .eq (.reg 58) (.lit 0))
  , .scalar (.binop 59 .mul (.reg 59) (.reg 55))
  , .scalar (.binop 60 .sub (.lit 1) (.reg 59))
  , .scalar (.binop rSqf .mul (.reg rSqf) (.reg 60)) ]

def sieveFactorBlock : List AInstr :=
  sieveFactorHead ++ sieveFactorMux ++ sieveFactorTail

theorem sieveBody_factor_split (c : Cfg) :
    c.sieveBody.take 25 = c.sieveBody.take 11 ++ sieveFactorBlock := by
  simp [Cfg.sieveBody, sieveFactorBlock, sieveFactorHead, sieveFactorMux,
    sieveFactorTail, muxBody]

def sieveHit (m p : Nat) : Nat := if m % p = 0 then 1 else 0

theorem sieveFactorHead_run (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hpPos : 0 < st.regs 53)
    (hmM : st.regs rM < M) (hpM : st.regs 53 < M) :
    let out := arun idx st sieveFactorHead
    out.regs 55 = sieveHit (st.regs rM) (st.regs 53) ∧
      out.regs 56 = st.regs rM / st.regs 53 ∧
      out.regs rM = st.regs rM ∧ out.regs 53 = st.regs 53 := by
  have hpNe : st.regs 53 ≠ 0 := Nat.ne_of_gt hpPos
  have hremM : st.regs rM % st.regs 53 < M :=
    Nat.lt_trans (Nat.mod_lt _ hpPos) hpM
  have hremMod : (st.regs rM % st.regs 53) % M =
      st.regs rM % st.regs 53 := Nat.mod_eq_of_lt hremM
  have hdivM : st.regs rM / st.regs 53 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hmM
  have hdivMod : (st.regs rM / st.regs 53) % M =
      st.regs rM / st.regs 53 := Nat.mod_eq_of_lt hdivM
  have hremMod9 : (st.regs 9 % st.regs 53) % M =
      st.regs 9 % st.regs 53 := by simpa [rM] using hremMod
  have hdivMod9 : (st.regs 9 / st.regs 53) % M =
      st.regs 9 / st.regs 53 := by simpa [rM] using hdivMod
  simp [sieveFactorHead, sieveHit, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
    rM, hgate, hpNe, hremMod9, hdivMod9]
  split <;> decide

def sieveNextM (m p : Nat) : Nat :=
  if sieveHit m p = 1 then m / p else m

theorem sieveFactorMux_run (idx : Nat) (st : AState) (m p : Nat)
    (hhit : st.regs 55 = sieveHit m p)
    (hquot : st.regs 56 = m / p) (hm : st.regs rM = m)
    (hword : ∀ j, st.regs j < M) :
    let out := arun idx st sieveFactorMux
    out.regs rM = sieveNextM m p ∧ out.arr = st.arr := by
  have hhitBit : sieveHit m p ≤ 1 := by
    unfold sieveHit
    split <;> omega
  have hmux := muxBody_arun idx st rM 55 56 rM 57
    (by decide) (by decide) (by decide) (by decide)
    (by rw [hhit]; exact hhitBit) hword
  simpa [sieveFactorMux, sieveNextM, hhit, hquot, hm] using hmux

def sieveRepeated (m p hit : Nat) : Nat :=
  ((if m % p = 0 then 1 else 0) * hit) % M

def sieveKeep (m p hit : Nat) : Nat :=
  (1 + (M - sieveRepeated m p hit)) % M

def sieveFactorStep (s : SieveFactorState) (p : Nat) : SieveFactorState :=
  let hit := sieveHit s.m p
  let m' := sieveNextM s.m p
  { m := m'
    par := (s.par ^^^ hit) % M
    sqf := (s.sqf * sieveKeep m' p hit) % M }

theorem sieveFactorTail_run (idx : Nat) (st : AState)
    (hpPos : 0 < st.regs 53) (hpM : st.regs 53 < M) :
    let out := arun idx st sieveFactorTail
    out.regs rPar = (st.regs rPar ^^^ st.regs 55) % M ∧
      out.regs rSqf =
        (st.regs rSqf * sieveKeep (st.regs rM) (st.regs 53)
          (st.regs 55)) % M := by
  have hpNe : st.regs 53 ≠ 0 := Nat.ne_of_gt hpPos
  have hremM : st.regs rM % st.regs 53 < M := by
    exact Nat.lt_trans (Nat.mod_lt _ hpPos) hpM
  have hremMod : (st.regs rM % st.regs 53) % M =
      st.regs rM % st.regs 53 := Nat.mod_eq_of_lt hremM
  have hremMod9 : (st.regs 9 % st.regs 53) % M =
      st.regs 9 % st.regs 53 := by simpa [rM] using hremMod
  simp [sieveFactorTail, sieveKeep, sieveRepeated, arun, astep,
    InstrBlock.sdest, InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rM, rPar, rSqf, hpNe, hremMod9]
  rfl

theorem sieveFactorBlock_run (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hpPos : 0 < st.regs 53)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let before : SieveFactorState :=
      ⟨st.regs rM, st.regs rPar, st.regs rSqf⟩
    let out := arun idx st sieveFactorBlock
    out.regs rM = (sieveFactorStep before (st.regs 53)).m ∧
      out.regs rPar = (sieveFactorStep before (st.regs 53)).par ∧
      out.regs rSqf = (sieveFactorStep before (st.regs 53)).sqf ∧
      out.regs 53 = st.regs 53 ∧ out.arr = st.arr := by
  let headed := arun idx st sieveFactorHead
  let muxed := arun idx headed sieveFactorMux
  have hh := sieveFactorHead_run idx st hgate hpPos (hword rM) (hword 53)
  have hhw := arun_word idx sieveFactorHead st hword harr
  have hhM : headed.regs rM = st.regs rM := hh.2.2.1
  have hh53 : headed.regs 53 = st.regs 53 := hh.2.2.2
  have hm := sieveFactorMux_run idx headed (st.regs rM) (st.regs 53)
    hh.1 hh.2.1 hhM hhw.1
  have hmw := arun_word idx sieveFactorMux headed hhw.1 hhw.2
  have hm53 : muxed.regs 53 = st.regs 53 := by
    rw [show muxed.regs 53 = headed.regs 53 from
      ArrayRegFrame.arun_frame idx 53 sieveFactorMux (by rfl) headed, hh53]
  have hm55 : muxed.regs 55 = sieveHit (st.regs rM) (st.regs 53) := by
    rw [show muxed.regs 55 = headed.regs 55 from
      ArrayRegFrame.arun_frame idx 55 sieveFactorMux (by rfl) headed, hh.1]
  have hmPar : muxed.regs rPar = st.regs rPar := by
    rw [show muxed.regs rPar = headed.regs rPar from
      ArrayRegFrame.arun_frame idx rPar sieveFactorMux (by rfl) headed]
    exact ArrayRegFrame.arun_frame idx rPar sieveFactorHead (by rfl) st
  have hmSqf : muxed.regs rSqf = st.regs rSqf := by
    rw [show muxed.regs rSqf = headed.regs rSqf from
      ArrayRegFrame.arun_frame idx rSqf sieveFactorMux (by rfl) headed]
    exact ArrayRegFrame.arun_frame idx rSqf sieveFactorHead (by rfl) st
  have ht := sieveFactorTail_run idx muxed (by rw [hm53]; exact hpPos)
    (by rw [hm53]; exact hword 53)
  rw [sieveFactorBlock, arun_append, arun_append]
  change (arun idx muxed sieveFactorTail).regs rM = _ ∧ _
  dsimp only [sieveFactorStep]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show (arun idx muxed sieveFactorTail).regs rM = muxed.regs rM from
      ArrayRegFrame.arun_frame idx rM sieveFactorTail (by rfl) muxed, hm.1]
  · rw [ht.1, hmPar, hm55]
  · rw [ht.2, hmSqf, hm.1, hm53, hm55]
  · rw [show (arun idx muxed sieveFactorTail).regs 53 = muxed.regs 53 from
      ArrayRegFrame.arun_frame idx 53 sieveFactorTail (by rfl) muxed, hm53]
  · rw [show (arun idx muxed sieveFactorTail).arr = muxed.arr from
      arun_store_free_arr idx sieveFactorTail muxed (by rfl), hm.2]
    exact arun_store_free_arr idx sieveFactorHead st (by rfl)

def sieveFirst (pj : Nat) : Nat := if pj = 0 then 1 else 0

def sieveResetFirst : List AInstr :=
  [ .scalar (.binop 50 .eq (.reg rPj) (.lit 0))
  , .scalar (.binop 50 .mul (.reg 50) (.reg 40)) ]

theorem sieveResetFirst_run (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) :
    (arun idx st sieveResetFirst).regs 50 = sieveFirst (st.regs rPj) := by
  unfold sieveFirst
  have h1M : (1 : Nat) % M = 1 := by decide
  by_cases h : st.regs rPj = 0
  · have h8 : st.regs 8 = 0 := by simpa [rPj] using h
    simp [sieveResetFirst, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rPj, hgate, h8, h1M]
  · have h8 : st.regs 8 ≠ 0 := by simpa [rPj] using h
    simp [sieveResetFirst, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rPj, hgate, h8]

def sieveResetMux : List AInstr := muxBody rM 50 rN rM 51

def sieveResetKeep (first : Nat) : Nat := (1 + (M - first)) % M

def sieveResetPar (par first : Nat) : Nat :=
  (par * sieveResetKeep first) % M

def sieveResetSqf (sqf first : Nat) : Nat :=
  ((sqf * sieveResetKeep first) % M + first) % M

def sieveResetTail : List AInstr :=
  [ .scalar (.binop 52 .sub (.lit 1) (.reg 50))
  , .scalar (.binop rPar .mul (.reg rPar) (.reg 52))
  , .scalar (.binop rSqf .mul (.reg rSqf) (.reg 52))
  , .scalar (.binop rSqf .add (.reg rSqf) (.reg 50)) ]

theorem sieveResetTail_run (idx : Nat) (st : AState) :
    let out := arun idx st sieveResetTail
    out.regs rPar = sieveResetPar (st.regs rPar) (st.regs 50) ∧
      out.regs rSqf = sieveResetSqf (st.regs rSqf) (st.regs 50) := by
  simp [sieveResetTail, sieveResetPar, sieveResetSqf, sieveResetKeep,
    arun, astep, InstrBlock.sdest, InstrBlock.sval, denoteOperand,
    denoteOp, AState.writeReg, rPar, rSqf]

def sieveResetLoad : List AInstr := [.load 53 rPj]

theorem sieveResetLoad_run (idx : Nat) (st : AState) :
    let out := arun idx st sieveResetLoad
    out.regs 53 = st.arr (st.regs rPj) ∧ out.arr = st.arr := by
  simp [sieveResetLoad, arun, astep, AState.writeReg]

def sieveResetBlock : List AInstr :=
  sieveResetFirst ++ sieveResetMux ++ sieveResetTail ++ sieveResetLoad

theorem sieveBody_reset_split (c : Cfg) :
    c.sieveBody.take 11 = sieveResetBlock := by
  simp [Cfg.sieveBody, sieveResetBlock, sieveResetFirst, sieveResetMux,
    sieveResetTail, sieveResetLoad, muxBody]

structure SieveLoadedState extends SieveFactorState where
  p : Nat

def sieveResetM (n m pj : Nat) : Nat :=
  if sieveFirst pj = 1 then n else m

def sieveResetStep (n m par sqf pj : Nat) (arr : Nat → Nat) :
    SieveLoadedState :=
  let first := sieveFirst pj
  { m := sieveResetM n m pj
    par := sieveResetPar par first
    sqf := sieveResetSqf sqf first
    p := arr pj }

theorem sieveResetBlock_run (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let model := sieveResetStep (st.regs rN) (st.regs rM)
      (st.regs rPar) (st.regs rSqf) (st.regs rPj) st.arr
    let out := arun idx st sieveResetBlock
    out.regs rM = model.m ∧ out.regs rPar = model.par ∧
      out.regs rSqf = model.sqf ∧ out.regs 53 = model.p ∧
      out.arr = st.arr := by
  let firsted := arun idx st sieveResetFirst
  let muxed := arun idx firsted sieveResetMux
  let tailed := arun idx muxed sieveResetTail
  have hf := sieveResetFirst_run idx st hgate
  have hfw := arun_word idx sieveResetFirst st hword harr
  have hfbit : firsted.regs 50 ≤ 1 := by
    rw [hf]
    unfold sieveFirst
    split <;> omega
  have hmux := muxBody_arun idx firsted rM 50 rN rM 51
    (by decide) (by decide) (by decide) (by decide) hfbit hfw.1
  have hfn : firsted.regs rN = st.regs rN :=
    ArrayRegFrame.arun_frame idx rN sieveResetFirst (by rfl) st
  have hfm : firsted.regs rM = st.regs rM :=
    ArrayRegFrame.arun_frame idx rM sieveResetFirst (by rfl) st
  have hmuxM : muxed.regs rM =
      (if firsted.regs 50 = 1 then firsted.regs rN else firsted.regs rM) := by
    simpa [muxed, sieveResetMux] using hmux.1
  have hm : muxed.regs rM =
      sieveResetM (st.regs rN) (st.regs rM) (st.regs rPj) := by
    rw [hmuxM, hf, hfn, hfm]
    rfl
  have hmw := arun_word idx sieveResetMux firsted hfw.1 hfw.2
  have hm50 : muxed.regs 50 = sieveFirst (st.regs rPj) := by
    rw [show muxed.regs 50 = firsted.regs 50 from
      ArrayRegFrame.arun_frame idx 50 sieveResetMux (by rfl) firsted, hf]
  have hmPar : muxed.regs rPar = st.regs rPar := by
    rw [show muxed.regs rPar = firsted.regs rPar from
      ArrayRegFrame.arun_frame idx rPar sieveResetMux (by rfl) firsted]
    exact ArrayRegFrame.arun_frame idx rPar sieveResetFirst (by rfl) st
  have hmSqf : muxed.regs rSqf = st.regs rSqf := by
    rw [show muxed.regs rSqf = firsted.regs rSqf from
      ArrayRegFrame.arun_frame idx rSqf sieveResetMux (by rfl) firsted]
    exact ArrayRegFrame.arun_frame idx rSqf sieveResetFirst (by rfl) st
  have ht := sieveResetTail_run idx muxed
  have htM : tailed.regs rM = sieveResetM (st.regs rN) (st.regs rM)
      (st.regs rPj) := by
    rw [show tailed.regs rM = muxed.regs rM from
      ArrayRegFrame.arun_frame idx rM sieveResetTail (by rfl) muxed, hm]
  have htPj : tailed.regs rPj = st.regs rPj := by
    rw [show tailed.regs rPj = muxed.regs rPj from
      ArrayRegFrame.arun_frame idx rPj sieveResetTail (by rfl) muxed]
    rw [show muxed.regs rPj = firsted.regs rPj from
      ArrayRegFrame.arun_frame idx rPj sieveResetMux (by rfl) firsted]
    exact ArrayRegFrame.arun_frame idx rPj sieveResetFirst (by rfl) st
  have hl := sieveResetLoad_run idx tailed
  have htailedArr : tailed.arr = st.arr :=
    arun_store_free_arr idx
      (sieveResetFirst ++ sieveResetMux ++ sieveResetTail) st (by rfl)
  rw [sieveResetBlock, arun_append, arun_append, arun_append]
  change (arun idx tailed sieveResetLoad).regs rM = _ ∧ _
  dsimp only [sieveResetStep, SieveLoadedState.toSieveFactorState]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show (arun idx tailed sieveResetLoad).regs rM = tailed.regs rM from
      ArrayRegFrame.arun_frame idx rM sieveResetLoad (by rfl) tailed, htM]
  · rw [show (arun idx tailed sieveResetLoad).regs rPar = tailed.regs rPar from
      ArrayRegFrame.arun_frame idx rPar sieveResetLoad (by rfl) tailed,
      ht.1, hmPar, hm50]
  · rw [show (arun idx tailed sieveResetLoad).regs rSqf = tailed.regs rSqf from
      ArrayRegFrame.arun_frame idx rSqf sieveResetLoad (by rfl) tailed,
      ht.2, hmSqf, hm50]
  · rw [hl.1, htPj, htailedArr]
  · rw [hl.2]
    exact htailedArr

def sieveRowStep (st : AState) : SieveFactorState :=
  let loaded := sieveResetStep (st.regs rN) (st.regs rM)
    (st.regs rPar) (st.regs rSqf) (st.regs rPj) st.arr
  sieveFactorStep loaded.toSieveFactorState loaded.p

theorem sieveBody_preCode_split (c : Cfg) :
    c.sieveBody.take 25 = sieveResetBlock ++ sieveFactorBlock := by
  rw [sieveBody_factor_split, sieveBody_reset_split]

theorem sieveBody_preCode_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1)
    (hprime : 0 < st.arr (st.regs rPj))
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let out := arun idx st (c.sieveBody.take 25)
    out.regs rM = (sieveRowStep st).m ∧
      out.regs rPar = (sieveRowStep st).par ∧
      out.regs rSqf = (sieveRowStep st).sqf ∧ out.arr = st.arr := by
  let reset := arun idx st sieveResetBlock
  have hr := sieveResetBlock_run idx st hgate hword harr
  have hrM : reset.regs rM =
      sieveResetM (st.regs rN) (st.regs rM) (st.regs rPj) := by
    simpa [sieveResetStep] using hr.1
  have hrPar : reset.regs rPar =
      sieveResetPar (st.regs rPar) (sieveFirst (st.regs rPj)) := by
    simpa [sieveResetStep] using hr.2.1
  have hrSqf : reset.regs rSqf =
      sieveResetSqf (st.regs rSqf) (sieveFirst (st.regs rPj)) := by
    simpa [sieveResetStep] using hr.2.2.1
  have hrw := arun_word idx sieveResetBlock st hword harr
  have hrGate : reset.regs 40 = 1 := by
    rw [show reset.regs 40 = st.regs 40 from
      ArrayRegFrame.arun_frame idx 40 sieveResetBlock (by rfl) st, hgate]
  have hrP : reset.regs 53 = st.arr (st.regs rPj) := hr.2.2.2.1
  have hf := sieveFactorBlock_run idx reset hrGate (by rw [hrP]; exact hprime)
    hrw.1 hrw.2
  rw [sieveBody_preCode_split, arun_append]
  change (arun idx reset sieveFactorBlock).regs rM = _ ∧ _
  unfold sieveRowStep
  dsimp only [sieveResetStep, SieveLoadedState.toSieveFactorState]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hrM, hrPar, hrSqf, hrP] using hf.1
  · simpa only [hrM, hrPar, hrSqf, hrP] using hf.2.1
  · simpa only [hrM, hrPar, hrSqf, hrP] using hf.2.2.1
  · rw [hf.2.2.2.2, hr.2.2.2.2]

theorem sieveBody_prefix_code_model (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1)
    (hprime : 0 < st.arr (st.regs rPj))
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    (arun idx st (c.sieveBody.take 29)).regs 63 =
      sieveCodeOf (sieveRowStep st).m (sieveRowStep st).par
        (sieveRowStep st).sqf := by
  let pre := arun idx st (c.sieveBody.take 25)
  have hp := sieveBody_preCode_run c idx st hgate hprime hword harr
  rw [sieveBody_code_split, arun_append, sieveCodeBlock_run]
  change sieveCodeOf (pre.regs rM) (pre.regs rPar) (pre.regs rSqf) = _
  rw [hp.1, hp.2.1, hp.2.2.1]

theorem sieveBody_last_model_store (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hpj : st.regs rPj = c.pn - 1)
    (hprime : 0 < st.arr (st.regs rPj))
    (hpnM : c.pn < M) (haddrM : st.regs rN + c.muBase < M)
    (hnNextM : st.regs rN + 1 < M)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let code := sieveCodeOf (sieveRowStep st).m (sieveRowStep st).par
      (sieveRowStep st).sqf
    let out := arun idx st c.sieveBody
    out.arr (st.regs rN + c.muBase) = code ∧
      (∀ j, j ≠ st.regs rN + c.muBase → out.arr j = st.arr j) ∧
      out.regs rPj = 0 ∧ out.regs rN = st.regs rN + 1 := by
  have hcode29 := sieveBody_prefix_code_model c idx st hgate hprime hword harr
  have hcode30 : (arun idx st (c.sieveBody.take 30)).regs 63 =
      sieveCodeOf (sieveRowStep st).m (sieveRowStep st).par
        (sieveRowStep st).sqf := by
    rw [sieveBody_prefix_last_split, arun_append]
    rw [show (arun idx (arun idx st (c.sieveBody.take 29))
        (sieveLastTest c)).regs 63 =
          (arun idx st (c.sieveBody.take 29)).regs 63 from
      ArrayRegFrame.arun_frame idx 63 (sieveLastTest c) (by rfl) _]
    exact hcode29
  have hs := sieveBody_last_computed_store c idx st hgate hpj hpnM haddrM
    hnNextM hword harr
  simpa [hcode30] using hs

end LeanCompCert.Ports.CDEMAbelSievePrefix

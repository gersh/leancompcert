import LeanCompCert.Ports.CDEMAbelOuter

/-! # Bounded active CDEM resident-table construction -/

namespace LeanCompCert.Ports.CDEMAbelSieve

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives
open LeanCompCert.Ports.CDEMAbelOuter

def sieveCommitGate : List AInstr :=
  [.scalar (.binop 64 .mul (.reg 64) (.reg 40))]

theorem sieveCommitGate_active (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hlast : st.regs 64 = 1) :
    (arun idx st sieveCommitGate).regs 64 = 1 := by
  have h1M : (1 : Nat) % M = 1 := by decide
  simp only [sieveCommitGate, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
    hgate, hlast, Nat.one_mul, h1M, Option.getD_some, if_pos]

def sieveCommitHead (c : Cfg) : List AInstr :=
  [.scalar (.binop 65 .add (.reg rN) (.lit c.muBase))]

theorem sieveCommitHead_run (c : Cfg) (idx : Nat) (st : AState)
    (haddrM : st.regs rN + c.muBase < M) :
    (arun idx st (sieveCommitHead c)).regs 65 = st.regs rN + c.muBase := by
  have haddrMod : (st.regs rN + c.muBase) % M =
      st.regs rN + c.muBase := Nat.mod_eq_of_lt haddrM
  have haddrMod7 : (st.regs 7 + c.muBase) % M =
      st.regs 7 + c.muBase := by simpa [rN] using haddrMod
  have hmuMod : c.muBase % M = c.muBase := Nat.mod_eq_of_lt (by omega)
  simp only [sieveCommitHead, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, rN,
    hmuMod, haddrMod7, Option.getD_some, if_pos]

def sieveCommitMux : List AInstr := muxBody 66 64 65 rZero 67

theorem sieveCommitMux_active (idx : Nat) (st : AState) (addr : Nat)
    (hgate : st.regs 64 = 1) (haddr : st.regs 65 = addr)
    (hword : ∀ j, st.regs j < M) :
    let out := arun idx st sieveCommitMux
    out.regs 66 = addr ∧ out.arr = st.arr := by
  have hm := muxBody_arun idx st 66 64 65 rZero 67
    (by decide) (by decide) (by decide) (by decide) (by omega) hword
  simpa [sieveCommitMux, hgate, haddr] using hm

def sieveCommitZero : List AInstr :=
  [.scalar (.binop 68 .sub (.lit 1) (.reg 64))]

theorem sieveCommitZero_active (idx : Nat) (st : AState)
    (hlast : st.regs 64 = 1) :
    (arun idx st sieveCommitZero).regs 68 = 0 := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hsub : (1 + (M - 1)) % M = 0 := by decide
  simp only [sieveCommitZero, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, hlast,
    h1M, hsub, Option.getD_some, if_pos]

def sieveCommitSink (c : Cfg) : List AInstr :=
  [.scalar (.binop 69 .mul (.reg 68) (.lit c.sink))]

theorem sieveCommitSink_zero (c : Cfg) (idx : Nat) (st : AState)
    (hzero : st.regs 68 = 0) :
    (arun idx st (sieveCommitSink c)).regs 69 = 0 := by
  simp only [sieveCommitSink, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, hzero,
    Nat.zero_mul, Nat.zero_mod, Option.getD_some, if_pos]

def sieveCommitAdd : List AInstr :=
  [.scalar (.binop 66 .add (.reg 66) (.reg 69))]

theorem sieveCommitAdd_zero (idx : Nat) (st : AState) (addr : Nat)
    (haddr : st.regs 66 = addr) (hzero : st.regs 69 = 0)
    (haddrM : addr < M) :
    (arun idx st sieveCommitAdd).regs 66 = addr := by
  have hmod : addr % M = addr := Nat.mod_eq_of_lt haddrM
  simp only [sieveCommitAdd, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, haddr,
    hzero, Nat.add_zero, hmod, Option.getD_some, if_pos]

def sieveCommitAddress (c : Cfg) : List AInstr :=
  sieveCommitGate ++ sieveCommitHead c ++ sieveCommitMux ++
    sieveCommitZero ++ sieveCommitSink c ++ sieveCommitAdd

theorem sieveCommitAddress_active (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hlast : st.regs 64 = 1)
    (haddrM : st.regs rN + c.muBase < M)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let out := arun idx st (sieveCommitAddress c)
    out.regs 64 = 1 ∧ out.regs 66 = st.regs rN + c.muBase ∧
      out.arr = st.arr := by
  let gated := arun idx st sieveCommitGate
  let headed := arun idx gated (sieveCommitHead c)
  let muxed := arun idx headed sieveCommitMux
  let zeroed := arun idx muxed sieveCommitZero
  let sunk := arun idx zeroed (sieveCommitSink c)
  have hgw := arun_word idx sieveCommitGate st hword harr
  have hg64 := sieveCommitGate_active idx st hgate hlast
  have hgN : gated.regs rN = st.regs rN :=
    ArrayRegFrame.arun_frame idx rN sieveCommitGate (by rfl) st
  have hh := sieveCommitHead_run c idx gated (by rw [hgN]; exact haddrM)
  have hhw := arun_word idx (sieveCommitHead c) gated hgw.1 hgw.2
  have hh64 : headed.regs 64 = 1 := by
    rw [show headed.regs 64 = gated.regs 64 from
      ArrayRegFrame.arun_frame idx 64 (sieveCommitHead c) (by rfl) gated,
      hg64]
  have hhAddr : headed.regs 65 = st.regs rN + c.muBase := by
    rw [hh, hgN]
  have hm := sieveCommitMux_active idx headed
    (st.regs rN + c.muBase) hh64 hhAddr hhw.1
  have hmw := arun_word idx sieveCommitMux headed hhw.1 hhw.2
  have hm64 : muxed.regs 64 = 1 := by
    rw [show muxed.regs 64 = headed.regs 64 from
      ArrayRegFrame.arun_frame idx 64 sieveCommitMux (by rfl) headed,
      hh64]
  have hz := sieveCommitZero_active idx muxed hm64
  have hzw := arun_word idx sieveCommitZero muxed hmw.1 hmw.2
  have hz66 : zeroed.regs 66 = st.regs rN + c.muBase := by
    rw [show zeroed.regs 66 = muxed.regs 66 from
      ArrayRegFrame.arun_frame idx 66 sieveCommitZero (by rfl) muxed,
      hm.1]
  have hs := sieveCommitSink_zero c idx zeroed hz
  have hsw := arun_word idx (sieveCommitSink c) zeroed hzw.1 hzw.2
  have hs66 : sunk.regs 66 = st.regs rN + c.muBase := by
    rw [show sunk.regs 66 = zeroed.regs 66 from
      ArrayRegFrame.arun_frame idx 66 (sieveCommitSink c) (by rfl) zeroed,
      hz66]
  have ha := sieveCommitAdd_zero idx sunk (st.regs rN + c.muBase)
    hs66 hs haddrM
  rw [sieveCommitAddress, arun_append, arun_append, arun_append,
    arun_append, arun_append]
  change (arun idx sunk sieveCommitAdd).regs 64 = 1 ∧ _
  refine ⟨?_, ha, ?_⟩
  · rw [show (arun idx sunk sieveCommitAdd).regs 64 = sunk.regs 64 from
      ArrayRegFrame.arun_frame idx 64 sieveCommitAdd (by rfl) sunk]
    rw [show sunk.regs 64 = zeroed.regs 64 from
      ArrayRegFrame.arun_frame idx 64 (sieveCommitSink c) (by rfl) zeroed]
    rw [show zeroed.regs 64 = muxed.regs 64 from
      ArrayRegFrame.arun_frame idx 64 sieveCommitZero (by rfl) muxed, hm64]
  · exact arun_store_free_arr idx (sieveCommitAddress c) st (by rfl)

def sieveCommitStore : List AInstr := [.store 66 63]

theorem sieveCommitStore_run (idx : Nat) (st : AState) (addr : Nat)
    (haddr : st.regs 66 = addr) :
    let out := arun idx st sieveCommitStore
    out.arr addr = st.regs 63 ∧
      ∀ j, j ≠ addr → out.arr j = st.arr j := by
  dsimp only
  constructor
  · simp [sieveCommitStore, arun, astep, AState.writeArr, haddr]
  · intro j hj
    simp [sieveCommitStore, arun, astep, AState.writeArr, haddr, hj]

def sieveCursorAdd : List AInstr :=
  [.scalar (.binop 70 .add (.reg rPj) (.reg 40))]

def sieveCursorZero : List AInstr :=
  [.scalar (.binop 71 .sub (.lit 1) (.reg 64))]

theorem sieveCursorZero_active (idx : Nat) (st : AState)
    (hlast : st.regs 64 = 1) :
    (arun idx st sieveCursorZero).regs 71 = 0 := by
  have h1M : (1 : Nat) % M = 1 := by decide
  have hsub : (1 + (M - 1)) % M = 0 := by decide
  simp only [sieveCursorZero, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, hlast,
    h1M, hsub, Option.getD_some, if_pos]

def sieveCursorPrime : List AInstr :=
  [.scalar (.binop rPj .mul (.reg 70) (.reg 71))]

theorem sieveCursorPrime_zero (idx : Nat) (st : AState)
    (hzero : st.regs 71 = 0) :
    (arun idx st sieveCursorPrime).regs rPj = 0 := by
  simp only [sieveCursorPrime, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, rPj,
    hzero, Nat.mul_zero, Nat.zero_mod, Option.getD_some, if_pos]

def sieveCursorN : List AInstr :=
  [.scalar (.binop rN .add (.reg rN) (.reg 64))]

theorem sieveCursorN_active (idx : Nat) (st : AState)
    (hlast : st.regs 64 = 1) (hnNextM : st.regs rN + 1 < M) :
    (arun idx st sieveCursorN).regs rN = st.regs rN + 1 := by
  have hmod : (st.regs rN + 1) % M = st.regs rN + 1 :=
    Nat.mod_eq_of_lt hnNextM
  have hmod7 : (st.regs 7 + 1) % M = st.regs 7 + 1 := by
    simpa [rN] using hmod
  simp only [sieveCursorN, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, rN,
    hlast, hmod7, Option.getD_some, if_pos]

def sieveCommitCursor : List AInstr :=
  sieveCursorAdd ++ sieveCursorZero ++ sieveCursorPrime ++ sieveCursorN

theorem sieveCommitCursor_active (idx : Nat) (st : AState)
    (hlast : st.regs 64 = 1) (hnNextM : st.regs rN + 1 < M) :
    let out := arun idx st sieveCommitCursor
    out.arr = st.arr ∧ out.regs rPj = 0 ∧
      out.regs rN = st.regs rN + 1 := by
  let added := arun idx st sieveCursorAdd
  let zeroed := arun idx added sieveCursorZero
  let primed := arun idx zeroed sieveCursorPrime
  have ha64 : added.regs 64 = 1 := by
    rw [show added.regs 64 = st.regs 64 from
      ArrayRegFrame.arun_frame idx 64 sieveCursorAdd (by rfl) st, hlast]
  have haN : added.regs rN = st.regs rN :=
    ArrayRegFrame.arun_frame idx rN sieveCursorAdd (by rfl) st
  have hz := sieveCursorZero_active idx added ha64
  have hzN : zeroed.regs rN = st.regs rN := by
    rw [show zeroed.regs rN = added.regs rN from
      ArrayRegFrame.arun_frame idx rN sieveCursorZero (by rfl) added, haN]
  have hz64 : zeroed.regs 64 = 1 := by
    rw [show zeroed.regs 64 = added.regs 64 from
      ArrayRegFrame.arun_frame idx 64 sieveCursorZero (by rfl) added, ha64]
  have hp := sieveCursorPrime_zero idx zeroed hz
  have hpN : primed.regs rN = st.regs rN := by
    rw [show primed.regs rN = zeroed.regs rN from
      ArrayRegFrame.arun_frame idx rN sieveCursorPrime (by rfl) zeroed, hzN]
  have hp64 : primed.regs 64 = 1 := by
    rw [show primed.regs 64 = zeroed.regs 64 from
      ArrayRegFrame.arun_frame idx 64 sieveCursorPrime (by rfl) zeroed, hz64]
  have hn := sieveCursorN_active idx primed hp64 (by rw [hpN]; exact hnNextM)
  rw [sieveCommitCursor, arun_append, arun_append, arun_append]
  change (arun idx primed sieveCursorN).arr = st.arr ∧ _
  refine ⟨?_, ?_, ?_⟩
  · exact arun_store_free_arr idx sieveCommitCursor st (by rfl)
  · rw [show (arun idx primed sieveCursorN).regs rPj = primed.regs rPj from
      ArrayRegFrame.arun_frame idx rPj sieveCursorN (by rfl) primed, hp]
  · rw [hn, hpN]

theorem sieveInactiveSuffix_commit_split (c : Cfg) :
    sieveInactiveSuffix c =
      sieveCommitAddress c ++ sieveCommitStore ++ sieveCommitCursor := by
  simp [sieveInactiveSuffix, sieveCommitAddress, sieveCommitGate,
    sieveCommitHead, sieveCommitMux, sieveCommitZero, sieveCommitSink,
    sieveCommitAdd, sieveCommitStore, sieveCommitCursor, sieveCursorAdd,
    sieveCursorZero, sieveCursorPrime, sieveCursorN, muxBody]

theorem sieve_active_last_store (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hlast : st.regs 64 = 1)
    (haddrM : st.regs rN + c.muBase < M)
    (hnNextM : st.regs rN + 1 < M)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let out := arun idx st (sieveInactiveSuffix c)
    out.arr (st.regs rN + c.muBase) = st.regs 63 ∧
      (∀ j, j ≠ st.regs rN + c.muBase → out.arr j = st.arr j) ∧
      out.regs rPj = 0 ∧ out.regs rN = st.regs rN + 1 := by
  let pre := arun idx st (sieveCommitAddress c)
  let stored := arun idx pre sieveCommitStore
  have hp := sieveCommitAddress_active c idx st hgate hlast haddrM hword harr
  have hp63 : pre.regs 63 = st.regs 63 :=
    ArrayRegFrame.arun_frame idx 63 (sieveCommitAddress c) (by rfl) st
  have hpN : pre.regs rN = st.regs rN :=
    ArrayRegFrame.arun_frame idx rN (sieveCommitAddress c) (by rfl) st
  have hs := sieveCommitStore_run idx pre (st.regs rN + c.muBase) hp.2.1
  have hs64 : stored.regs 64 = 1 := by
    rw [show stored.regs 64 = pre.regs 64 from
      ArrayRegFrame.arun_frame idx 64 sieveCommitStore (by rfl) pre, hp.1]
  have hsN : stored.regs rN = st.regs rN := by
    rw [show stored.regs rN = pre.regs rN from
      ArrayRegFrame.arun_frame idx rN sieveCommitStore (by rfl) pre, hpN]
  have ht := sieveCommitCursor_active idx stored hs64 (by
    rw [hsN]
    exact hnNextM)
  rw [sieveInactiveSuffix_commit_split, arun_append, arun_append]
  change
    (arun idx stored sieveCommitCursor).arr
          (st.regs rN + c.muBase) = st.regs 63 ∧ _
  constructor
  · rw [ht.1, hs.1, hp63]
  constructor
  · intro j hj
    rw [ht.1]
    exact hs.2 j hj
  · exact ⟨ht.2.1, ht.2.2.trans (congrArg (fun n => n + 1) hsN)⟩

theorem sieveBody_last_store (c : Cfg) (idx : Nat) (st : AState)
    (code : Nat)
    (hgate : (arun idx st (c.sieveBody.take 30)).regs 40 = 1)
    (hlast : (arun idx st (c.sieveBody.take 30)).regs 64 = 1)
    (hn : (arun idx st (c.sieveBody.take 30)).regs rN = st.regs rN)
    (hcode : (arun idx st (c.sieveBody.take 30)).regs 63 = code)
    (haddrM : st.regs rN + c.muBase < M)
    (hnNextM : st.regs rN + 1 < M)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let out := arun idx st c.sieveBody
    out.arr (st.regs rN + c.muBase) = code ∧
      (∀ j, j ≠ st.regs rN + c.muBase → out.arr j = st.arr j) ∧
      out.regs rPj = 0 ∧ out.regs rN = st.regs rN + 1 := by
  let pre := arun idx st (c.sieveBody.take 30)
  have hpw := arun_word idx (c.sieveBody.take 30) st hword harr
  have hpa : pre.arr = st.arr :=
    arun_store_free_arr idx (c.sieveBody.take 30) st (by rfl)
  have hs := sieve_active_last_store c idx pre hgate hlast (by
      rw [hn]
      exact haddrM) (by rw [hn]; exact hnNextM) hpw.1 hpw.2
  rw [sieveBody_inactive_split, arun_append]
  change
    (arun idx pre (sieveInactiveSuffix c)).arr
          (st.regs rN + c.muBase) = code ∧ _
  constructor
  · rw [← hn, hs.1, hcode]
  constructor
  · intro j hj
    rw [hs.2.1 j (by rw [hn]; exact hj), hpa]
  · exact ⟨hs.2.2.1, hs.2.2.2.trans (congrArg (fun n => n + 1) hn)⟩

def sieveLastTest (c : Cfg) : List AInstr :=
  [.scalar (.binop 64 .eq (.reg rPj) (.lit (c.pn - 1)))]

theorem sieveBody_prefix_last_split (c : Cfg) :
    c.sieveBody.take 30 = c.sieveBody.take 29 ++ sieveLastTest c := by
  simp [Cfg.sieveBody, sieveLastTest, muxBody]

theorem sieveLastTest_run (c : Cfg) (idx : Nat) (st : AState)
    (hpnM : c.pn < M) (hpj : st.regs rPj = c.pn - 1) :
    (arun idx st (sieveLastTest c)).regs 64 = 1 := by
  have hlastM : c.pn - 1 < M := by omega
  have hlastMod : (c.pn - 1) % M = c.pn - 1 :=
    Nat.mod_eq_of_lt hlastM
  have hpj8 : st.regs 8 = c.pn - 1 := by simpa [rPj] using hpj
  simp only [sieveLastTest, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg, rPj,
    hlastMod, hpj8, if_pos, Option.getD_some]

theorem sieveBody_last_computed_store (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hpj : st.regs rPj = c.pn - 1)
    (hpnM : c.pn < M) (haddrM : st.regs rN + c.muBase < M)
    (hnNextM : st.regs rN + 1 < M)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let code := (arun idx st (c.sieveBody.take 30)).regs 63
    let out := arun idx st c.sieveBody
    out.arr (st.regs rN + c.muBase) = code ∧
      (∀ j, j ≠ st.regs rN + c.muBase → out.arr j = st.arr j) ∧
      out.regs rPj = 0 ∧ out.regs rN = st.regs rN + 1 := by
  let pre29 := arun idx st (c.sieveBody.take 29)
  have hpj29 : pre29.regs rPj = c.pn - 1 := by
    rw [show pre29.regs rPj = st.regs rPj from
      ArrayRegFrame.arun_frame idx rPj (c.sieveBody.take 29) (by rfl) st,
      hpj]
  have hlast := sieveLastTest_run c idx pre29 hpnM hpj29
  have hgate30 : (arun idx st (c.sieveBody.take 30)).regs 40 = 1 := by
    rw [show (arun idx st (c.sieveBody.take 30)).regs 40 = st.regs 40 from
      ArrayRegFrame.arun_frame idx 40 (c.sieveBody.take 30) (by rfl) st,
      hgate]
  have hn30 : (arun idx st (c.sieveBody.take 30)).regs rN = st.regs rN :=
    ArrayRegFrame.arun_frame idx rN (c.sieveBody.take 30) (by rfl) st
  apply sieveBody_last_store c idx st
    ((arun idx st (c.sieveBody.take 30)).regs 63) hgate30
  · rw [sieveBody_prefix_last_split, arun_append]
    exact hlast
  · exact hn30
  · rfl
  · exact haddrM
  · exact hnNextM
  · exact hword
  · exact harr

end LeanCompCert.Ports.CDEMAbelSieve

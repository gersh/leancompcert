import LeanCompCert.Ports.R2RuntimeMarkDenote
import LeanCompCert.Ports.LogFixRoundSemantics
import LeanCompCert.Ports.R2SegLnFixConvert
import LeanCompCert.Verified.InstrRename
import LeanCompCert.Verified.ArrayRegFrame
import LeanCompCert.Verified.LogFixedBounds

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

theorem rootPackDecode_run (c : R2Cfg) (index : Nat) (s : AState)
    (hi : index < (r2RootPackProgram c).loopCount) :
    let out := arun index s rootPackDecode
    out.regs 11 = rootPackN index ∧
      out.regs 12 = rootPackRound index ∧
      out.regs 13 = (if rootPackRound index = 0 then 1 else 0) ∧
      out.regs 15 = (if rootPackRound index + 1 = runtimeScale then 1 else 0) ∧
      out.regs 16 = s.arr (rootPackN index) ∧
      out.regs 17 = (if s.arr (rootPackN index) = 0 then 1 else 0) ∧
      out.arr = s.arr := by
  have hb := rootPack_index_bounds (index := index) (by
    simpa [r2RootPackProgram] using hi)
  have hiM : index % M = index := Nat.mod_eq_of_lt hb.1
  have hsM : runtimeScale % M = runtimeScale := Nat.mod_eq_of_lt (by decide)
  have hsne : runtimeScale % M ≠ 0 := by rw [hsM]; decide
  have hnM : rootPackN index % M = rootPackN index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hb.2.1 (by decide))
  have hrM : rootPackRound index % M = rootPackRound index :=
    Nat.mod_eq_of_lt (Nat.lt_trans hb.2.2 (by decide))
  have hnRawM : (index / runtimeScale + 2) % M =
      index / runtimeScale + 2 := by
    simpa [rootPackN] using hnM
  have hroundRaw :
      (if runtimeScale % M = 0 then none
        else some (index % M % (runtimeScale % M))).getD 0 =
          rootPackRound index := by
    rw [if_neg hsne, Option.getD_some, hiM, hsM]
    rfl
  have hrSuccM : (rootPackRound index + 1) % M =
      rootPackRound index + 1 := Nat.mod_eq_of_lt (by
    exact Nat.lt_trans (Nat.add_lt_add_right hb.2.2 1) (by decide))
  have h24M : 24 % M = 24 := Nat.mod_eq_of_lt (by decide)
  have h24ne : 24 % M ≠ 0 := by rw [h24M]; decide
  have hqM : (index / 24) % M = index / 24 :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hb.1)
  have hnRaw24M : (index / 24 + 2) % M = index / 24 + 2 := by
    simpa [runtimeScale] using hnRawM
  have hNdecode :
      ((if 24 % M = 0 then none else some (index / (24 % M) % M)).getD 0 + 2) % M =
        index / 24 + 2 := by
    rw [if_neg h24ne, Option.getD_some, h24M, hqM, hnRaw24M]
  have hRdecode :
      (if 24 % M = 0 then none else some (index % (24 % M) % M)).getD 0 =
        index % 24 := by
    rw [if_neg h24ne, Option.getD_some, h24M]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  simp [rootPackDecode, arun, astep, sval, sdest, denoteOperand, denoteOp,
    AState.writeReg, rootPackN, rootPackRound, runtimeScale, hiM, hsM,
    hsne, hnM, hnRawM, hroundRaw, hrM, hrSuccM, hNdecode, hRdecode,
    h24M, h24ne]
  have hr24M : index % 24 % M = index % 24 := by
    simpa [rootPackRound, runtimeScale] using hrM
  have hrSucc24M : (index % 24 + 1) % M = index % 24 + 1 := by
    simpa [rootPackRound, runtimeScale] using hrSuccM
  have hfinish :
      (if (index % 24 + 1) % M = 24 then 1 else 0) =
        if index % 24 = 23 then 1 else 0 := by
    rw [hrSucc24M]
    have hrlt : index % 24 < 24 := Nat.mod_lt _ (by decide)
    by_cases h : index % 24 = 23 <;> simp [h] <;> omega
  exact ⟨hnRaw24M, hr24M,
    congrArg (fun z => if z = 0 then 1 else 0) hr24M,
    hfinish, congrArg s.arr hnRaw24M,
    congrArg (fun z => if s.arr z = 0 then 1 else 0) hnRaw24M⟩

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

/-! ## Incremental exponent and mantissa initialization -/

theorem rootPackExponentS_run (k : Nat) (s : RegState)
    (n e th start : Nat)
    (h11 : s 11 = n) (h13 : s 13 = start)
    (he : s rpEx = e) (hth : s rpTh = th)
    (hstart : start = 0 ∨ start = 1)
    (heM : e + 1 < M) (hthM : th + th < M) :
    let bump := if th ≤ n then start else 0
    let out := srun k s rootPackExponentS
    out rpEx = e + bump ∧ out rpTh = th + bump * th := by
  have he0M : e < M := by omega
  have hth0M : th < M := by omega
  have he' : s 2 = e := by simpa only [rpEx] using he
  have hth' : s 3 = th := by simpa only [rpTh] using hth
  rcases hstart with rfl | rfl
  · by_cases hn : th ≤ n <;>
      simp [rootPackExponentS, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, h11, h13, he', hth', hn,
        Nat.mod_eq_of_lt he0M, Nat.mod_eq_of_lt hth0M, rpEx, rpTh]
  · by_cases hn : th ≤ n <;>
      simp [rootPackExponentS, srun, RegState.set, sdest, sval,
        denoteOperand, denoteOp, h11, h13, he', hth', hn,
        Nat.mod_eq_of_lt he0M, Nat.mod_eq_of_lt hth0M,
        Nat.mod_eq_of_lt heM, Nat.mod_eq_of_lt hthM, rpEx, rpTh]

theorem rootPackExponent_run (k : Nat) (s : AState)
    (n e th start : Nat)
    (h11 : s.regs 11 = n) (h13 : s.regs 13 = start)
    (he : s.regs rpEx = e) (hth : s.regs rpTh = th)
    (hstart : start = 0 ∨ start = 1)
    (heM : e + 1 < M) (hthM : th + th < M) :
    let bump := if th ≤ n then start else 0
    let out := arun k s rootPackExponent
    out.regs rpEx = e + bump ∧ out.regs rpTh = th + bump * th ∧
      out.arr = s.arr := by
  rw [rootPackExponent,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := rootPackExponentS_run k s.regs n e th start
    h11 h13 he hth hstart heM hthM
  exact ⟨h.1, h.2, rfl⟩

theorem rootPackMantissaInitS_run (k : Nat) (s : RegState)
    (n e start x a : Nat)
    (h11 : s 11 = n) (h13 : s 13 = start) (he : s rpEx = e)
    (hx : s rpXm = x) (ha : s rpAa = a)
    (hstart : start = 0 ∨ start = 1) (he62 : e ≤ 62)
    (hnorm : n <<< (62 - e) < M) (hxM : x < M) (haM : a < M) :
    let out := srun k s rootPackMantissaInitS
    (out rpXm = if start = 1 then n <<< (62 - e) else x) ∧
      (out rpAa = if start = 1 then 0 else a) := by
  have hsub : (62 + (M - e)) % M = 62 - e := by
    have hs := LeanCompCert.Verified.BlockDefined.denoteOp_sub_of_le
      (a := 62) (b := e) he62 (by decide)
    exact Option.some.inj hs
  have hmask : (63 : Nat) % M = 63 := by decide
  have hshift : (62 - e) &&& 63 = 62 - e := by
    have hlt : 62 - e < 64 := by omega
    change (62 - e) &&& (2 ^ 6 - 1) = 62 - e
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  have hshiftM : 62 - e < M :=
    Nat.lt_trans (show 62 - e < 64 by omega) (by decide)
  have he' : s 2 = e := by simpa only [rpEx] using he
  have hx' : s 5 = x := by simpa only [rpXm] using hx
  have ha' : s 6 = a := by simpa only [rpAa] using ha
  have hOnePred : 1 + (M - 1) = M := by omega
  rcases hstart with rfl | rfl
  · simp [rootPackMantissaInitS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h11, h13, he', hx', ha', hsub, hmask, hshift,
      Nat.mod_eq_of_lt hshiftM, Nat.mod_eq_of_lt hnorm,
      Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt haM, hOnePred,
      rpEx, rpXm, rpAa]
    all_goals simp [Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt haM,
      Nat.add_mod, Nat.mul_mod, hOnePred]
  · simp [rootPackMantissaInitS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h11, h13, he', hx', ha', hsub, hmask, hshift,
      Nat.mod_eq_of_lt hshiftM, Nat.mod_eq_of_lt hnorm,
      Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt haM, hOnePred,
      rpEx, rpXm, rpAa]
    all_goals simp [Nat.mod_eq_of_lt hnorm, Nat.add_mod, Nat.mul_mod,
      hOnePred]

theorem rootPackMantissaInit_run (k : Nat) (s : AState)
    (n e start x a : Nat)
    (h11 : s.regs 11 = n) (h13 : s.regs 13 = start)
    (he : s.regs rpEx = e) (hx : s.regs rpXm = x) (ha : s.regs rpAa = a)
    (hstart : start = 0 ∨ start = 1) (he62 : e ≤ 62)
    (hnorm : n <<< (62 - e) < M) (hxM : x < M) (haM : a < M) :
    let out := arun k s rootPackMantissaInit
    (out.regs rpXm = if start = 1 then n <<< (62 - e) else x) ∧
      (out.regs rpAa = if start = 1 then 0 else a) ∧ out.arr = s.arr := by
  rw [rootPackMantissaInit,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  have h := rootPackMantissaInitS_run k s.regs n e start x a
    h11 h13 he hx ha hstart he62 hnorm hxM haM
  exact ⟨h.1, h.2, rfl⟩

/-- Exact composition of the two initialization slices.  This theorem is
symbolic in the candidate and persistent state; it does not enumerate the
production table. -/
theorem rootPackRoundInit_run (k : Nat) (s : AState)
    (n e th start x a : Nat)
    (h11 : s.regs 11 = n) (h13 : s.regs 13 = start)
    (he : s.regs rpEx = e) (hth : s.regs rpTh = th)
    (hx : s.regs rpXm = x) (ha : s.regs rpAa = a)
    (hstart : start = 0 ∨ start = 1)
    (heM : e + 1 < M) (hthM : th + th < M)
    (he62 : e + (if th ≤ n then start else 0) ≤ 62)
    (hnorm : n <<< (62 - (e + (if th ≤ n then start else 0))) < M)
    (hxM : x < M) (haM : a < M) :
    let bump := if th ≤ n then start else 0
    let out := arun k s rootPackRoundInit
    out.regs rpEx = e + bump ∧
      out.regs rpTh = th + bump * th ∧
      out.regs rpXm =
        (if start = 1 then n <<< (62 - (e + bump)) else x) ∧
      out.regs rpAa = (if start = 1 then 0 else a) ∧
      out.arr = s.arr := by
  let bump := if th ≤ n then start else 0
  let mid := arun k s rootPackExponent
  have hExp := rootPackExponent_run k s n e th start
    h11 h13 he hth hstart heM hthM
  dsimp only at hExp
  have h11mid : mid.regs 11 = n := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 11 rootPackExponent (by decide) s).trans h11
  have h13mid : mid.regs 13 = start := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k 13 rootPackExponent (by decide) s).trans h13
  have hxmid : mid.regs rpXm = x := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rpXm rootPackExponent (by decide) s).trans hx
  have hamid : mid.regs rpAa = a := by
    exact (LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rpAa rootPackExponent (by decide) s).trans ha
  have hMant := rootPackMantissaInit_run k mid n (e + bump) start x a
    h11mid h13mid (by simpa only [mid, bump] using hExp.1)
    hxmid hamid hstart (by simpa only [bump] using he62)
    (by simpa only [bump] using hnorm) hxM haM
  dsimp only at hMant
  rw [rootPackRoundInit, arun_append]
  change
    (arun k mid rootPackMantissaInit).regs rpEx = e + bump ∧
      (arun k mid rootPackMantissaInit).regs rpTh = th + bump * th ∧
      _
  have hExFrame := LeanCompCert.Verified.ArrayRegFrame.arun_frame
    k rpEx rootPackMantissaInit (by decide) mid
  have hThFrame := LeanCompCert.Verified.ArrayRegFrame.arun_frame
    k rpTh rootPackMantissaInit (by decide) mid
  exact ⟨hExFrame.trans hExp.1, hThFrame.trans hExp.2.1,
    hMant.1, hMant.2.1, hMant.2.2.trans hExp.2.2⟩

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

theorem rootPack_logIter_fst_range (x0 : Nat)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63) : ∀ rounds : Nat,
    B62 ≤ (logIter x0 rounds).1 ∧ (logIter x0 rounds).1 < B63 := by
  intro rounds
  induction rounds with
  | zero => exact ⟨hxlo, hxhi⟩
  | succ rounds ih =>
      simpa only [logIter, logStep] using logMant_range ih.1 ih.2

/-- Symbolic telescope for an arbitrary list of compiled round invocations.
Only the list length is used; no production candidate range is evaluated. -/
theorem rootPack_foldl_logRound_from_iter (indices : List Nat) (s : AState)
    (x0 : Nat) (j : Nat)
    (hx : s.regs rpXm = (logIter x0 j).1)
    (ha : s.regs rpAa = (logIter x0 j).2)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63)
    (hcount : j + indices.length ≤ 62) :
    let out := indices.foldl (fun st k => arun k st rootPackLogRound) s
    out.regs rpXm = (logIter x0 (j + indices.length)).1 ∧
      out.regs rpAa = (logIter x0 (j + indices.length)).2 ∧
      out.arr = s.arr := by
  induction indices generalizing s j with
  | nil =>
      simp only [List.foldl, List.length_nil, Nat.add_zero]
      exact ⟨hx, ha, trivial⟩
  | cons k ks ih =>
      have hj : j < 62 := by
        simp only [List.length_cons] at hcount
        omega
      have haLt := logIter_snd_lt_two_pow x0 j
      have haBound : (logIter x0 j).2 < B62 := by
        have hjPow : 2 ^ j ≤ 2 ^ 61 :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hpow : (2 : Nat) ^ 61 < B62 := by decide
        omega
      have hrange := rootPack_logIter_fst_range x0 hxlo hxhi j
      let next := arun k s rootPackLogRound
      have hstep := rootPackLogRound_run_of_range k s
        (logIter x0 j).1 (logIter x0 j).2 hx ha
        hrange.1 hrange.2 haBound
      dsimp only at hstep
      have hxNext : next.regs rpXm = (logIter x0 (j + 1)).1 := by
        simpa only [next, logIter, logStep] using hstep.1
      have haNext : next.regs rpAa = (logIter x0 (j + 1)).2 := by
        simpa only [next, logIter, logStep, Nat.shiftLeft_eq,
          Nat.pow_one, Nat.mul_comm] using hstep.2.1
      have hrest : j + 1 + ks.length ≤ 62 := by
        simp only [List.length_cons] at hcount
        omega
      have hout := ih next (j + 1) hxNext haNext hrest
      dsimp only at hout
      simp only [List.foldl, List.length_cons]
      have hindex : j + 1 + ks.length = j + (ks.length + 1) := by omega
      exact ⟨hout.1.trans (congrArg (fun z => (logIter x0 z).1) hindex),
        hout.2.1.trans (congrArg (fun z => (logIter x0 z).2) hindex),
        hout.2.2.trans hstep.2.2⟩

theorem rootPack_foldl_logRound_24 (indices : List Nat) (s : AState)
    (x0 : Nat) (hlen : indices.length = runtimeScale)
    (hx : s.regs rpXm = x0) (ha : s.regs rpAa = 0)
    (hxlo : B62 ≤ x0) (hxhi : x0 < B63) :
    let out := indices.foldl (fun st k => arun k st rootPackLogRound) s
    out.regs rpXm = (logIter x0 runtimeScale).1 ∧
      out.regs rpAa = logFrac runtimeScale x0 ∧ out.arr = s.arr := by
  have h := rootPack_foldl_logRound_from_iter indices s x0 0
    (by simpa [logIter] using hx) (by simpa [logIter] using ha)
    hxlo hxhi (by simpa [hlen, runtimeScale])
  simpa only [Nat.zero_add, hlen, logFrac] using h

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

/-! ## Fixed-log assembly and natural-log composition -/

theorem rootPackLnPrefixS_run (k : Nat) (s : RegState) (e a : Nat)
    (he : s rpEx = e) (ha : s rpAa = a)
    (heM : e * 2 ^ runtimeScale < M)
    (hsumM : e * 2 ^ runtimeScale + a < M) :
    (srun k s rootPackLnPrefixS) 46 = e * 2 ^ runtimeScale + a := by
  have h24M : runtimeScale % M = runtimeScale := by decide
  have he' : s 2 = e := by simpa only [rpEx] using he
  have ha' : s 6 = a := by simpa only [rpAa] using ha
  change
    ((((s 2 <<< (runtimeScale % M)) % M) + s 6) % M) =
      e * 2 ^ runtimeScale + a
  rw [he', ha', h24M, Nat.shiftLeft_eq, Nat.mod_eq_of_lt heM,
    Nat.mod_eq_of_lt hsumM]

theorem rootPackLnPrefixS_logFix_run (k : Nat) (s : RegState) (n : Nat)
    (he : s rpEx = Nat.log2 n)
    (ha : s rpAa = logFrac runtimeScale
      (n <<< (62 - Nat.log2 n)))
    (hfix : logFix runtimeScale n < 2 ^ 30) :
    (srun k s rootPackLnPrefixS) 46 = logFix runtimeScale n := by
  have hfixM : logFix runtimeScale n < M :=
    Nat.lt_trans hfix (by decide)
  have heM : Nat.log2 n * 2 ^ runtimeScale < M := by
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (by
      simpa only [logFix] using hfixM)
  have hp := rootPackLnPrefixS_run k s (Nat.log2 n)
    (logFrac runtimeScale (n <<< (62 - Nat.log2 n))) he ha heM (by
      simpa only [logFix] using hfixM)
  simpa only [logFix] using hp

theorem rootPackLnS_logFix_run (k : Nat) (s : RegState) (n : Nat)
    (he : s rpEx = Nat.log2 n)
    (ha : s rpAa = logFrac runtimeScale
      (n <<< (62 - Nat.log2 n)))
    (hfix : logFix runtimeScale n < 2 ^ 30) :
    (srun k s rootPackLnS) 57 =
      LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale n := by
  let mid := srun k s rootPackLnPrefixS
  have hprefix := rootPackLnPrefixS_logFix_run k s n he ha hfix
  have hconvert := rootPackLnConvertS_logFix_run k mid runtimeScale n
    hfix (by simpa only [mid] using hprefix)
  rw [rootPackLnS, srun_append]
  exact hconvert

theorem rootPackLn_logFix_run (k : Nat) (s : AState) (n : Nat)
    (he : s.regs rpEx = Nat.log2 n)
    (ha : s.regs rpAa = logFrac runtimeScale
      (n <<< (62 - Nat.log2 n)))
    (hfix : logFix runtimeScale n < 2 ^ 30) :
    let out := arun k s rootPackLn
    out.regs 57 = LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale n ∧
      out.arr = s.arr := by
  rw [rootPackLn, LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackLnS_logFix_run k s.regs n he ha hfix, rfl⟩

/-! ## Selected-entry store islands -/

theorem rootPackStoreGateS_run (k : Nat) (s : RegState)
    (finish prime : Nat)
    (h15 : s 15 = finish) (h17 : s 17 = prime)
    (hfinish : finish = 0 ∨ finish = 1)
    (hprime : prime = 0 ∨ prime = 1) :
    (srun k s rootPackStoreGateS) 58 = finish * prime := by
  have h1M : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt (by decide)
  rcases hfinish with rfl | rfl <;> rcases hprime with rfl | rfl <;>
    simp [rootPackStoreGateS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h15, h17, h1M]

theorem rootPackStoreGate_run (k : Nat) (s : AState)
    (finish prime : Nat)
    (h15 : s.regs 15 = finish) (h17 : s.regs 17 = prime)
    (hfinish : finish = 0 ∨ finish = 1)
    (hprime : prime = 0 ∨ prime = 1) :
    let out := arun k s rootPackStoreGate
    out.regs 58 = finish * prime ∧ out.arr = s.arr := by
  rw [rootPackStoreGate,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackStoreGateS_run k s.regs finish prime
    h15 h17 hfinish hprime, rfl⟩

theorem rootPackStoreTargetS_run (c : R2Cfg) (k : Nat) (s : RegState)
    (hit w : Nat) (h58 : s 58 = hit) (hw : s rpWrite = w)
    (hhit : hit = 0 ∨ hit = 1)
    (htable : c.tableBase < M) (hsink : c.streamSink < M)
    (hwtable : w + c.tableBase < M) :
    (srun k s (rootPackStoreTargetS c)) 63 =
      if hit = 1 then w + c.tableBase else c.streamSink := by
  have htableM : c.tableBase % M = c.tableBase := Nat.mod_eq_of_lt htable
  have hsinkM : c.streamSink % M = c.streamSink := Nat.mod_eq_of_lt hsink
  have hwtableM : (w + c.tableBase) % M = w + c.tableBase :=
    Nat.mod_eq_of_lt hwtable
  have hwM : w % M = w := Nat.mod_eq_of_lt (by omega)
  have hw' : s 4 = w := by simpa only [rpWrite] using hw
  have hOnePred : 1 + (M - 1) = M := by omega
  rcases hhit with rfl | rfl <;>
    simp [rootPackStoreTargetS, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, h58, hw', htableM, hsinkM, hwtableM,
      hwM, hOnePred, rpWrite]

theorem rootPackStoreTarget_run (c : R2Cfg) (k : Nat) (s : AState)
    (hit w : Nat) (h58 : s.regs 58 = hit) (hw : s.regs rpWrite = w)
    (hhit : hit = 0 ∨ hit = 1)
    (htable : c.tableBase < M) (hsink : c.streamSink < M)
    (hwtable : w + c.tableBase < M) :
    let out := arun k s (rootPackStoreTarget c)
    out.regs 63 =
      (if hit = 1 then w + c.tableBase else c.streamSink) ∧
      out.arr = s.arr := by
  rw [rootPackStoreTarget,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackStoreTargetS_run c k s.regs hit w h58 hw hhit
    htable hsink hwtable, rfl⟩

theorem rootPackStoreValueS_run (k : Nat) (s : RegState) (n ln : Nat)
    (hn : s 11 = n) (hln : s 57 = ln)
    (hshift : ln * 2 ^ valBits < M)
    (hlow : n + ln * 2 ^ valBits < M)
    (hpack : packEntry n ln 1 < M) :
    (srun k s rootPackStoreValueS) 66 = packEntry n ln 1 := by
  have hvalM : valBits % M = valBits := Nat.mod_eq_of_lt (by decide)
  have hshiftM : (ln * 2 ^ valBits) % M = ln * 2 ^ valBits :=
    Nat.mod_eq_of_lt hshift
  have hlowM : (n + ln * 2 ^ valBits) % M = n + ln * 2 ^ valBits :=
    Nat.mod_eq_of_lt hlow
  have hpackEq : packEntry n ln 1 = n + ln * 2 ^ valBits + B63 := by
    rw [packEntry, Nat.one_mul, B63_eq]
  have hsum : n + ln * 2 ^ valBits + B63 < M := by
    rw [← hpackEq]
    exact hpack
  have h64 : (srun k s [rootPackStoreShiftI]) 64 =
      ln * 2 ^ valBits := by
    rw [show [rootPackStoreShiftI] = [] ++ [rootPackStoreShiftI] by rfl,
      LeanCompCert.Verified.RegFrame.srun_read_last k 64 []
        rootPackStoreShiftI (by rfl) s]
    change ((s 57 <<< (valBits % M)) % M) = ln * 2 ^ valBits
    rw [hln, hvalM, Nat.shiftLeft_eq, hshiftM]
  have h11frame : (srun k s [rootPackStoreShiftI]) 11 = s 11 :=
    LeanCompCert.Verified.RegFrame.srun_frame k 11
      [rootPackStoreShiftI] (by decide) s
  have h65 : (srun k s [rootPackStoreShiftI, rootPackStoreLowI]) 65 =
      n + ln * 2 ^ valBits := by
    rw [show [rootPackStoreShiftI, rootPackStoreLowI] =
        [rootPackStoreShiftI] ++ [rootPackStoreLowI] by rfl,
      LeanCompCert.Verified.RegFrame.srun_read_last k 65
        [rootPackStoreShiftI] rootPackStoreLowI (by rfl) s]
    change
      (((srun k s [rootPackStoreShiftI]) 11 +
        (srun k s [rootPackStoreShiftI]) 64) % M) =
          n + ln * 2 ^ valBits
    rw [h11frame, hn, h64, hlowM]
  rw [show rootPackStoreValueS =
      [rootPackStoreShiftI, rootPackStoreLowI] ++ [rootPackStoreFlagI] by rfl,
    LeanCompCert.Verified.RegFrame.srun_read_last k 66
      [rootPackStoreShiftI, rootPackStoreLowI] rootPackStoreFlagI (by rfl) s]
  rw [rootPackStoreFlagI]
  calc
    sval k (srun k s [rootPackStoreShiftI, rootPackStoreLowI])
        (.binop 66 .add (.reg 65) (.lit B63)) =
        n + ln * 2 ^ valBits + B63 :=
      LeanCompCert.Verified.BlockDefined.sval_binop_val
        (by
          rw [LeanCompCert.Verified.BlockDefined.denoteOperand_reg, h65])
        (LeanCompCert.Verified.BlockDefined.denoteOperand_lit_of_lt
          k _ (by decide))
        (LeanCompCert.Verified.BlockDefined.denoteOp_add_of_lt hsum)
    _ = packEntry n ln 1 := hpackEq.symm

theorem rootPackStoreValue_run (k : Nat) (s : AState) (n ln : Nat)
    (hn : s.regs 11 = n) (hln : s.regs 57 = ln)
    (hshift : ln * 2 ^ valBits < M)
    (hlow : n + ln * 2 ^ valBits < M)
    (hpack : packEntry n ln 1 < M) :
    let out := arun k s rootPackStoreValue
    out.regs 66 = packEntry n ln 1 ∧ out.arr = s.arr := by
  rw [rootPackStoreValue,
    LeanCompCert.Verified.ArrayScalarBlock.arun_lift]
  exact ⟨rootPackStoreValueS_run k s.regs n ln hn hln
    hshift hlow hpack, rfl⟩

theorem rootPackStoreCommit_run (k : Nat) (s : AState)
    (target value w hit : Nat)
    (h63 : s.regs 63 = target) (h66 : s.regs 66 = value)
    (hw : s.regs rpWrite = w) (h58 : s.regs 58 = hit)
    (hsum : w + hit < M) :
    let out := arun k s rootPackStoreCommit
    out.regs rpWrite = w + hit ∧
      ∀ x, out.arr x = if x = target then value else s.arr x := by
  have hsumM : (w + hit) % M = w + hit := Nat.mod_eq_of_lt hsum
  have hw' : s.regs 4 = w := by simpa only [rpWrite] using hw
  simp [rootPackStoreCommit, arun, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, AState.writeArr,
    h63, h66, hw', h58, hsumM, rpWrite]

#print axioms rootPackDecode_defined
#print axioms rootPackRoundInit_defined
#print axioms rootPackLogRound_defined
#print axioms rootPackLn_defined
#print axioms rootPackDecode_run
#print axioms rootPackExponentS_run
#print axioms rootPackExponent_run
#print axioms rootPackMantissaInitS_run
#print axioms rootPackMantissaInit_run
#print axioms rootPackRoundInit_run
#print axioms rootPackLogReg_injective
#print axioms rootPackLogRoundS_run_of_range
#print axioms rootPackLogRound_run_of_range
#print axioms rootPack_logIter_fst_range
#print axioms rootPack_foldl_logRound_from_iter
#print axioms rootPack_foldl_logRound_24
#print axioms rootPackLnReg_injective
#print axioms rootPackLnConvertS_logFix_run
#print axioms rootPackLnConvert_logFix_run
#print axioms rootPackLnPrefixS_run
#print axioms rootPackLnPrefixS_logFix_run
#print axioms rootPackLnS_logFix_run
#print axioms rootPackLn_logFix_run
#print axioms rootPackStoreGateS_run
#print axioms rootPackStoreGate_run
#print axioms rootPackStoreTargetS_run
#print axioms rootPackStoreTarget_run
#print axioms rootPackStoreValueS_run
#print axioms rootPackStoreValue_run
#print axioms rootPackStoreCommit_run

end LeanCompCert.Ports.R2SegSieve

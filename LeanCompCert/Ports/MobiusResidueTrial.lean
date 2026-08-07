import LeanCompCert.Ports.MertensCDEM
import LeanCompCert.Ports.MobiusResidueScalar
import LeanCompCert.Verified.RegFrame

/-!
# A fully denoted trial-division producer for the live Möbius residue

The segmented sieve remains the production algorithm, but its global
mark-table invariant is not yet proved.  `MertensCDEM`, by contrast, already
has a complete denotation theorem for fixed-round trial division.  This file
composes that proved producer with the proved live residue, giving a slow but
sound and arbitrarily shardable fallback whose compiled trace has no missing
sieve-to-signal arrow.

The first stage below is deliberately small: it materializes the four signal
registers from `MertensCDEM`'s final trial state.  Later the scalar residue is
appended without retranscribing any of its fifty instructions.
-/

namespace LeanCompCert.Ports.MobiusResidueTrial

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.MertensCDEM
open LeanCompCert.Verified.RegFrame

/-- Materialize `n`, the positive/negative Möbius bits, and the last-round
gate from the trial state left by `MertensCDEM.body`. -/
def signalBlock (c : Cfg) : List Instr :=
  [ .mov 65 (.reg 9)
  , .binop 133 .eq (.reg 6) (.lit (c.rounds - 1))
  , .binop 81 .ne (.reg 2) (.lit 1)
  , .binop 82 .bxor (.reg 4) (.reg 81)
  , .binop 83 .sub (.lit 1) (.reg 3)
  , .binop 84 .sub (.lit 1) (.reg 82)
  , .binop 79 .mul (.reg 83) (.reg 84)
  , .binop 79 .mul (.reg 133) (.reg 79)
  , .binop 80 .mul (.reg 83) (.reg 82)
  , .binop 80 .mul (.reg 133) (.reg 80) ]

/-- The mathematical signal belonging to one flattened trial round. -/
def roundSig (c : Cfg) (idx : Nat) (a : Abs) : Sig :=
  let t := (gstep c idx a).t
  let last := if idx % c.rounds = c.rounds - 1 then 1 else 0
  ⟨c.lo + idx / c.rounds, last * muPlus t, last * muMinus t, last⟩

/-- The decoded round and candidate survive the rest of `MertensCDEM.body`.
The proof erases the suffix by destination-set checks; it does not unfold the
row-check arithmetic. -/
theorem baseStep_decode (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hs : ∀ j, s j < M)
    (hidx : idx < c.len * c.rounds) :
    (step c idx s) 6 = idx % c.rounds ∧
      (step c idx s) 9 = c.lo + idx / c.rounds := by
  have hA := bodyA_spec c idx s hadm hs hidx
  have hsplit : body c = bodyA c ++ (bodyB ++ bodyC c) := by
    simp only [body, List.append_assoc]
  constructor
  · rw [step, hsplit, srun_frame_append idx 6 (bodyA c)
      (bodyB ++ bodyC c) (by rfl)]
    exact hA.2.2.1
  · rw [step, hsplit, srun_frame_append idx 9 (bodyA c)
      (bodyB ++ bodyC c) (by rfl)]
    exact hA.2.2.2.2.1

private theorem bit_cases {x : Nat} (hx : x ≤ 1) : x = 0 ∨ x = 1 := by omega

private theorem bit_xor_le (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) :
    x ^^^ y ≤ 1 := by
  rcases bit_cases hx with rfl | rfl <;>
    rcases bit_cases hy with rfl | rfl <;> decide

private theorem bit_mod (x : Nat) (hx : x ≤ 1) : x % M = x :=
  Nat.mod_eq_of_lt (by have := ArrayFoldBridge.one_lt_M; omega)

private theorem one_sub_bit_mod (x : Nat) (hx : x ≤ 1) :
    (1 + (M - x)) % M = 1 - x := by
  rcases bit_cases hx with rfl | rfl
  · rw [show 1 + (M - 0) = 1 + M by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by have := ArrayFoldBridge.one_lt_M; omega)
  · rw [show 1 + (M - 1) = M by have := M_pos; omega, Nat.mod_self]

private theorem mul_bit_mod (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1) :
    (x * y) % M = x * y := by
  exact Nat.mod_eq_of_lt (by
    have h := Nat.mul_le_mul hx hy
    have := ArrayFoldBridge.one_lt_M
    omega)

set_option maxHeartbeats 1000000 in
/-- The ten scalar instructions expose exactly `roundSig`. -/
theorem signal_read (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) :
    MobiusResidueScalar.readSig (srun idx (step c idx s) (signalBlock c)) =
      roundSig c idx (obs s) := by
  obtain ⟨hs, h0, h3, h4⟩ := hI
  have hobs := body_obs c idx s hadm hs h0 h3 h4 hidx
  have hbits := gstep_bits c idx (obs s) h0 h3 h4
  have hdec := baseStep_decode c idx s hadm hs hidx
  have ht3 : (step c idx s) 3 = (gstep c idx (obs s)).t.sq := by
    change (obs (step c idx s)).t.sq = (gstep c idx (obs s)).t.sq
    rw [hobs]
  have ht4 : (step c idx s) 4 = (gstep c idx (obs s)).t.par := by
    change (obs (step c idx s)).t.par = (gstep c idx (obs s)).t.par
    rw [hobs]
  have ht2 : (step c idx s) 2 = (gstep c idx (obs s)).t.res := by
    change (obs (step c idx s)).t.res = (gstep c idx (obs s)).t.res
    rw [hobs]
  have ht3b : (gstep c idx (obs s)).t.sq ≤ 1 := hbits.2.1
  have ht4b : (gstep c idx (obs s)).t.par ≤ 1 := hbits.2.2
  have hrem : (if (step c idx s) 2 ≠ 1 then (1 : Nat) else 0) ≤ 1 := by
    split <;> omega
  have homega : (gstep c idx (obs s)).t.par ^^^
      (if (step c idx s) 2 ≠ 1 then 1 else 0) ≤ 1 :=
    bit_xor_le _ _ ht4b hrem
  have hs3 : (1 - (gstep c idx (obs s)).t.sq) ≤ 1 := by omega
  have hs4 : (1 - ((gstep c idx (obs s)).t.par ^^^
      (if (step c idx s) 2 ≠ 1 then 1 else 0))) ≤ 1 := by
    omega
  rw [ht2] at hrem homega hs4
  have hlast : (if idx % c.rounds = c.rounds - 1 then (1 : Nat) else 0) ≤ 1 := by
    split <;> omega
  have hplus : (1 - (gstep c idx (obs s)).t.sq) *
      (1 - ((gstep c idx (obs s)).t.par ^^^
        (if (gstep c idx (obs s)).t.res ≠ 1 then 1 else 0))) ≤ 1 := by
    exact Nat.le_trans (Nat.mul_le_mul hs3 hs4) (by omega)
  have hminus : (1 - (gstep c idx (obs s)).t.sq) *
      ((gstep c idx (obs s)).t.par ^^^
        (if (gstep c idx (obs s)).t.res ≠ 1 then 1 else 0)) ≤ 1 := by
    exact Nat.le_trans (Nat.mul_le_mul hs3 homega) (by omega)
  have hRm : (c.rounds - 1) % M = c.rounds - 1 :=
    Nat.mod_eq_of_lt (by have := hadm.divLt; omega)
  have h1M : (1 : Nat) % M = 1 := by decide
  simp only [MobiusResidueScalar.readSig, signalBlock, srun, sdest, sval, denoteOperand,
    denoteOp, RegState.set, Option.getD_some, reduceIte,
    Nat.reduceEqDiff, if_true, roundSig, hdec.1, hdec.2, ht3, ht4,
    muPlus, muMinus, omegaPar]
  simp only [hRm, h1M, ht2, one_sub_bit_mod _ ht3b,
    bit_mod _ homega, one_sub_bit_mod _ homega,
    mul_bit_mod _ _ hs3 hs4, mul_bit_mod _ _ hs3 homega,
    mul_bit_mod _ _ hlast hplus, mul_bit_mod _ _ hlast hminus]

/-! ## Composing the trial body with the live residue -/

/-- Successful instruction denotation has the same state as the total
`srun` instruction.  This direction needs no definedness hypothesis: success
itself supplies it. -/
private theorem denoteInstr_some_eq_srun (idx : Nat) (s s' : RegState)
    (i : Instr) (h : denoteInstr idx s i = some s') :
    s' = s.set (sdest i) (sval idx s i) := by
  cases i with
  | mov d src =>
      simp only [denoteInstr] at h
      cases h
      rfl
  | binop d op lhs rhs =>
      simp only [denoteInstr] at h
      cases hop : denoteOp op (denoteOperand idx s lhs)
          (denoteOperand idx s rhs) with
      | none => simp [hop] at h
      | some v =>
          simp [hop] at h
          subst s'
          simp only [sdest, sval, hop, Option.getD_some]

/-- A successful block lands in its `srun` state, including blocks containing
defined divisions. -/
private theorem denoteInstrs_some_eq_srun (idx : Nat) :
    ∀ (l : List Instr) (s s' : RegState),
      denoteInstrs idx s l = some s' → s' = srun idx s l := by
  intro l
  induction l with
  | nil =>
      intro s s' h
      simp only [denoteInstrs, Option.some.injEq] at h
      exact h.symm
  | cons i rest ih =>
      intro s s' h
      simp only [denoteInstrs] at h
      cases hi : denoteInstr idx s i with
      | none => simp [hi] at h
      | some sm =>
          simp only [hi] at h
          rw [srun_cons, ← denoteInstr_some_eq_srun idx s sm i hi]
          exact ih sm s' h

/-- Denotation composes across a named block boundary without unfolding
either block. -/
private theorem denoteInstrs_append_intro (idx : Nat) (s sm s' : RegState)
    (xs ys : List Instr)
    (hx : denoteInstrs idx s xs = some sm)
    (hy : denoteInstrs idx sm ys = some s') :
    denoteInstrs idx s (xs ++ ys) = some s' := by
  induction xs generalizing s sm with
  | nil =>
      simp only [denoteInstrs, Option.some.injEq] at hx
      subst sm
      exact hy
  | cons i rest ih =>
      simp only [List.cons_append, denoteInstrs] at hx ⊢
      cases hi : denoteInstr idx s i with
      | none => simp [hi] at hx
      | some sn =>
          simp only [hi] at hx ⊢
          exact ih sn sm hx hy

/-- State after one trial round and signal materialization, immediately
before the persistent residue executes. -/
def signalState (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (step c idx s) (signalBlock c)

/-- The complete scalar body: proved trial division, the four signal writes,
then the exact live residue extracted from the array program. -/
def fullBody (c : Cfg) (k : Nat) : List Instr :=
  body c ++ signalBlock c ++ MobiusResidueScalar.residue k

/-- Total state transformer corresponding to `fullBody`. -/
def fullStep (c : Cfg) (k idx : Nat) (s : RegState) : RegState :=
  srun idx (signalState c idx s) (MobiusResidueScalar.residue k)

/-- Named form of `signal_read`, preventing later composition proofs from
unfolding the ten-instruction signal block. -/
theorem signalState_readSig (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) :
    MobiusResidueScalar.readSig (signalState c idx s) =
      roundSig c idx (obs s) := by
  simpa only [signalState] using signal_read c idx s hadm hI hidx

private theorem signalBlock_denote (c : Cfg) (idx : Nat) (s : RegState) :
    denoteInstrs idx s (signalBlock c) = some (srun idx s (signalBlock c)) := by
  apply srun_correct
  intro i hi
  simp only [signalBlock, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

private theorem signalState_frame (c : Cfg) (idx r : Nat) (s : RegState)
    (hb : writes r (body c) = false)
    (hg : writes r (signalBlock c) = false) :
    signalState c idx s r = s r := by
  rw [signalState, srun_frame idx r (signalBlock c) hg, step,
    srun_frame idx r (body c) hb]

/-- The producer leaves all five persistent residue fields untouched. -/
theorem signalState_readRes (c : Cfg) (idx : Nat) (s : RegState) :
    MobiusResidueScalar.readRes (signalState c idx s) =
      MobiusResidueScalar.readRes s := by
  simp only [MobiusResidueScalar.readRes]
  rw [signalState_frame c idx ArraySegSieve.rTLo s (by rfl) (by rfl),
    signalState_frame c idx ArraySegSieve.rTHi s (by rfl) (by rfl),
    signalState_frame c idx ArraySegSieve.rCeil s (by rfl) (by rfl),
    signalState_frame c idx ArraySegSieve.rCeilSq s (by rfl) (by rfl),
    signalState_frame c idx ArraySegSieve.rMViol s (by rfl) (by rfl)]

/-- **One complete denoted round.**  The only partial residue operations are
division by the positive candidate and by the updated ceiling.  The latter
is stated in transparent model terms so a window invariant can discharge it
without inspecting machine registers. -/
theorem fullBody_denote (c : Cfg) (k idx : Nat) (s : RegState)
    (hadm : Admissible c) (hlo : 0 < c.lo) (hI : Inv s)
    (hidx : idx < c.len * c.rounds)
    (hc : celAfter (roundSig c idx (obs s))
      (MobiusResidueScalar.readRes s) ≠ 0) :
    denoteInstrs idx s (fullBody c k) = some (fullStep c k idx s) := by
  have hb := body_denote c idx s hadm hI.1 hidx
  have hg := signalBlock_denote c idx (step c idx s)
  have hsig := signalState_readSig c idx s hadm hI hidx
  have hn : signalState c idx s 65 ≠ 0 := by
    have hn' := congrArg Sig.n hsig
    simp only [MobiusResidueScalar.readSig] at hn'
    have hnval : signalState c idx s 65 = c.lo + idx / c.rounds :=
      hn'.trans rfl
    rw [hnval]
    exact Nat.ne_of_gt (Nat.add_pos_left hlo _)
  have hc' : (celStep (signalState c idx s 65)
      (signalState c idx s 103) (signalState c idx s 102)
      (signalState c idx s 133)).1 ≠ 0 := by
    rw [← MobiusResidueScalar.celAfter_read]
    have hres := signalState_readRes c idx s
    rw [hsig, hres]
    exact hc
  obtain ⟨sr, hr⟩ := MobiusResidueScalar.residue_defined
    k idx (signalState c idx s) hn hc'
  have hsr := denoteInstrs_some_eq_srun idx
    (MobiusResidueScalar.residue k) (signalState c idx s) sr hr
  subst sr
  rw [fullBody, List.append_assoc]
  apply denoteInstrs_append_intro idx s (step c idx s)
      (fullStep c k idx s) (body c)
      (signalBlock c ++ MobiusResidueScalar.residue k) hb
  apply denoteInstrs_append_intro idx (step c idx s)
      (signalState c idx s) (fullStep c k idx s)
      (signalBlock c) (MobiusResidueScalar.residue k) hg
  exact hr

/-- Reading the persistent fields after a complete denoted round gives the
transparent residue step driven by the trial-derived signal. -/
theorem fullStep_readRes (c : Cfg) (k idx : Nat) (s : RegState)
    (hadm : Admissible c) (hlo : 0 < c.lo) (hI : Inv s)
    (hidx : idx < c.len * c.rounds)
    (hc : celAfter (roundSig c idx (obs s))
      (MobiusResidueScalar.readRes s) ≠ 0) :
    MobiusResidueScalar.readRes (fullStep c k idx s) =
      resStep k (roundSig c idx (obs s))
        (MobiusResidueScalar.readRes s) := by
  have hn : signalState c idx s 65 ≠ 0 := by
    have hn' := congrArg Sig.n (signalState_readSig c idx s hadm hI hidx)
    simp only [MobiusResidueScalar.readSig] at hn'
    have hnval : signalState c idx s 65 = c.lo + idx / c.rounds :=
      hn'.trans rfl
    rw [hnval]
    exact Nat.ne_of_gt (Nat.add_pos_left hlo _)
  have hc' : (celStep (signalState c idx s 65)
      (signalState c idx s 103) (signalState c idx s 102)
      (signalState c idx s 133)).1 ≠ 0 := by
    rw [← MobiusResidueScalar.celAfter_read]
    have hsig := signalState_readSig c idx s hadm hI hidx
    have hres := signalState_readRes c idx s
    rw [hsig, hres]
    exact hc
  obtain ⟨sr, hres⟩ := MobiusResidueScalar.residue_defined
    k idx (signalState c idx s) hn hc'
  have hsr := denoteInstrs_some_eq_srun idx
    (MobiusResidueScalar.residue k) (signalState c idx s) sr hres
  subst sr
  have hr := MobiusResidueScalar.residue_denote k idx
    (signalState c idx s) (fullStep c k idx s) ?_ ?_ ?_
  · have hsig := signalState_readSig c idx s hadm hI hidx
    have hres := signalState_readRes c idx s
    simpa only [hsig, hres] using hr
  · exact hn
  · exact hc'
  · exact hres

/-! ## Joint observation -/

/-- The mathematical state carried by the combined checker. -/
structure FullAbs where
  base : Abs
  residue : Res
  deriving Repr, DecidableEq

theorem FullAbs.eq_of {x y : FullAbs} (hb : x.base = y.base)
    (hr : x.residue = y.residue) : x = y := by
  cases x
  cases y
  simp_all

/-- Read both the trial-division state and the persistent residue. -/
def fullObs (s : RegState) : FullAbs :=
  ⟨obs s, MobiusResidueScalar.readRes s⟩

/-- One mathematical round of the combined checker.  The residue consumes
the signal derived from the *same* trial round as the base update. -/
def fullGstep (c : Cfg) (k idx : Nat) (a : FullAbs) : FullAbs :=
  ⟨gstep c idx a.base, resStep k (roundSig c idx a.base) a.residue⟩

private theorem signalState_base_frame (c : Cfg) (idx r : Nat)
    (s : RegState) (hg : writes r (signalBlock c) = false) :
    signalState c idx s r = step c idx s r := by
  exact srun_frame idx r (signalBlock c) hg (step c idx s)

private theorem fullStep_base_frame (c : Cfg) (k idx r : Nat)
    (s : RegState)
    (hr : writes r (MobiusResidueScalar.residue k) = false) :
    fullStep c k idx s r = signalState c idx s r := by
  exact srun_frame idx r (MobiusResidueScalar.residue k) hr
    (signalState c idx s)

set_option maxRecDepth 2048

/-- The appended signal and residue blocks do not perturb the five base
registers observed by `MertensCDEM`. -/
theorem fullStep_obs (c : Cfg) (k idx : Nat) (s : RegState)
    (hadm : Admissible c) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) :
    obs (fullStep c k idx s) = gstep c idx (obs s) := by
  rw [← body_obs c idx s hadm hI.1 hI.2.1 hI.2.2.1 hI.2.2.2 hidx]
  apply Abs.eq_of
  · exact (fullStep_base_frame c k idx 0 s (by rfl)).trans
      (signalState_base_frame c idx 0 s (by rfl))
  · exact (fullStep_base_frame c k idx 1 s (by rfl)).trans
      (signalState_base_frame c idx 1 s (by rfl))
  · apply Trial.eq_of
    · exact (fullStep_base_frame c k idx 2 s (by rfl)).trans
        (signalState_base_frame c idx 2 s (by rfl))
    · exact (fullStep_base_frame c k idx 3 s (by rfl)).trans
        (signalState_base_frame c idx 3 s (by rfl))
    · exact (fullStep_base_frame c k idx 4 s (by rfl)).trans
        (signalState_base_frame c idx 4 s (by rfl))

/-- The base word/bit invariant survives the appended residue.  This is
independent of the residue's division guards because `fullStep` is the total
arithmetic state transformer; definedness is supplied separately by
`fullBody_denote`. -/
theorem fullStep_inv (c : Cfg) (k idx : Nat) (s : RegState)
    (hadm : Admissible c) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) : Inv (fullStep c k idx s) := by
  have hbase := step_inv c idx s hadm hI hidx
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact srun_lt_of_lt idx (MobiusResidueScalar.residue k)
      (signalState c idx s)
      (srun_lt_of_lt idx (signalBlock c) (step c idx s) hbase.1)
  · rw [fullStep_base_frame c k idx 0 s (by rfl),
      signalState_base_frame c idx 0 s (by rfl)]
    exact hbase.2.1
  · rw [fullStep_base_frame c k idx 3 s (by rfl),
      signalState_base_frame c idx 3 s (by rfl)]
    exact hbase.2.2.1
  · rw [fullStep_base_frame c k idx 4 s (by rfl),
      signalState_base_frame c idx 4 s (by rfl)]
    exact hbase.2.2.2

/-- **Joint one-round simulation.**  This packages the base and residue
observation equations as the step used by a fold bridge. -/
theorem fullStep_fullObs (c : Cfg) (k idx : Nat) (s : RegState)
    (hadm : Admissible c) (hlo : 0 < c.lo) (hI : Inv s)
    (hidx : idx < c.len * c.rounds)
    (hc : celAfter (roundSig c idx (obs s))
      (MobiusResidueScalar.readRes s) ≠ 0) :
    fullObs (fullStep c k idx s) = fullGstep c k idx (fullObs s) := by
  apply FullAbs.eq_of
  · exact fullStep_obs c k idx s hadm hI hidx
  · exact fullStep_readRes c k idx s hadm hlo hI hidx hc

/-! ## A finite, shardable compiled checker -/

/-- Seed the five persistent fields.  Values are ordinary `u64` literals and
are therefore normalized modulo `M` by the verified instruction semantics. -/
def residueInit (r : Res) : List Instr :=
  [ .mov 100 (.lit r.tLo)
  , .mov 101 (.lit r.tHi)
  , .mov 102 (.lit r.cel)
  , .mov 103 (.lit r.celSq)
  , .mov 104 (.lit r.viol) ]

/-- Fresh residue state: the accumulator is biased by `2^(64+k)`, the
ceiling recurrence starts at `⌈√1⌉ = 1`, and no test has failed. -/
def standardResidue (k : Nat) : Res := ⟨0, 2 ^ k, 1, 1, 0⟩

/-- Concrete entry state of a trial/residue shard. -/
def fullEntry (c : Cfg) (r : Res) : RegState :=
  srun 0 (entry c) (residueInit r)

/-- The executable finite checker.  Register `104` is the accumulated count
of failed residue inequalities. -/
def fullProgram (c : Cfg) (k : Nat) (r : Res) : Program :=
  { regCount := 172
  , loopCount := c.len * c.rounds
  , init := initBlock c ++ residueInit r
  , body := fullBody c k
  , epilogue := []
  , output := 104 }

theorem fullEntry_init (c : Cfg) (r : Res) :
    denoteInstrs 0 initialState (initBlock c ++ residueInit r) =
      some (fullEntry c r) := by
  apply denoteInstrs_append_intro 0 initialState (entry c) (fullEntry c r)
      (initBlock c) (residueInit r) (entry_init c)
  apply srun_correct
  intro i hi
  simp only [residueInit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem fullEntry_inv (c : Cfg) (r : Res) : Inv (fullEntry c r) := by
  have he := entry_inv c
  refine ⟨srun_lt_of_lt 0 (residueInit r) (entry c) he.1, ?_, ?_, ?_⟩
  · rw [fullEntry, srun_frame 0 0 (residueInit r) (by rfl)]
    exact he.2.1
  · rw [fullEntry, srun_frame 0 3 (residueInit r) (by rfl)]
    exact he.2.2.1
  · rw [fullEntry, srun_frame 0 4 (residueInit r) (by rfl)]
    exact he.2.2.2

/-- Exact safety condition for a finite trace.  It contains only bounded
natural-number computation.  Unlike a global analytic premise, it is
directly runnable; unlike one monolithic evaluation, its recursive shape can
be split at any list boundary. -/
def SafeRun (c : Cfg) (k : Nat) : List Nat → RegState → Prop
  | [], _ => True
  | idx :: rest, s =>
      celAfter (roundSig c idx (obs s))
          (MobiusResidueScalar.readRes s) ≠ 0 ∧
        SafeRun c k rest (fullStep c k idx s)

/-- Executable Boolean form of the exact safety certificate. -/
def safeCheck (c : Cfg) (k : Nat) : List Nat → RegState → Bool
  | [], _ => true
  | idx :: rest, s =>
      decide (celAfter (roundSig c idx (obs s))
          (MobiusResidueScalar.readRes s) ≠ 0) &&
        safeCheck c k rest (fullStep c k idx s)

theorem safeCheck_eq_true (c : Cfg) (k : Nat) (indices : List Nat)
    (s : RegState) :
    safeCheck c k indices s = true ↔ SafeRun c k indices s := by
  induction indices generalizing s with
  | nil => simp only [safeCheck, SafeRun]
  | cons idx rest ih =>
      simp only [safeCheck, SafeRun, Bool.and_eq_true, decide_eq_true_eq,
        ih (fullStep c k idx s)]

/-- Safety splits exactly where execution splits, which is the theorem used
to validate independent shards. -/
theorem safeRun_append (c : Cfg) (k : Nat) :
    ∀ (xs ys : List Nat) (s : RegState),
      SafeRun c k (xs ++ ys) s ↔
        SafeRun c k xs s ∧
          SafeRun c k ys (xs.foldl (fun s idx => fullStep c k idx s) s) := by
  intro xs
  induction xs with
  | nil => intro ys s; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons idx rest ih =>
      intro ys s
      simp only [List.cons_append, SafeRun, List.foldl_cons]
      rw [ih ys (fullStep c k idx s)]
      constructor
      · rintro ⟨hg, hr, hy⟩
        exact ⟨⟨hg, hr⟩, hy⟩
      · rintro ⟨⟨hg, hr⟩, hy⟩
        exact ⟨hg, hr, hy⟩

/-- A safe list of visited indices has a successful concrete trace equal to
the pure `fullStep` fold. -/
theorem safeRun_denote (c : Cfg) (k : Nat) (hlo : 0 < c.lo)
    (hadm : Admissible c) :
    ∀ (indices : List Nat) (s : RegState),
      (∀ idx ∈ indices, idx < c.len * c.rounds) → Inv s →
      SafeRun c k indices s →
      indices.foldlM (fun s idx => denoteInstrs idx s (fullBody c k)) s =
        some (indices.foldl (fun s idx => fullStep c k idx s) s) := by
  intro indices
  induction indices with
  | nil => intro s _ _ _; rfl
  | cons idx rest ih =>
      intro s hmem hI hsafe
      have hidx : idx < c.len * c.rounds := hmem idx (by simp)
      show (denoteInstrs idx s (fullBody c k)).bind
          (fun s => rest.foldlM
            (fun s idx => denoteInstrs idx s (fullBody c k)) s) = _
      rw [fullBody_denote c k idx s hadm hlo hI hidx hsafe.1]
      exact ih (fullStep c k idx s)
        (fun i hi => hmem i (by simp [hi]))
        (fullStep_inv c k idx s hadm hI hidx) hsafe.2

/-- The mathematical joint observation commutes with every safe finite
trace. -/
theorem safeRun_fullObs (c : Cfg) (k : Nat) (hlo : 0 < c.lo)
    (hadm : Admissible c) :
    ∀ (indices : List Nat) (s : RegState),
      (∀ idx ∈ indices, idx < c.len * c.rounds) → Inv s →
      SafeRun c k indices s →
      fullObs (indices.foldl (fun s idx => fullStep c k idx s) s) =
        indices.foldl (fun a idx => fullGstep c k idx a) (fullObs s) := by
  intro indices
  induction indices with
  | nil => intro s _ _ _; rfl
  | cons idx rest ih =>
      intro s hmem hI hsafe
      have hidx : idx < c.len * c.rounds := hmem idx (by simp)
      rw [List.foldl_cons,
        ih (fullStep c k idx s) (fun i hi => hmem i (by simp [hi]))
          (fullStep_inv c k idx s hadm hI hidx) hsafe.2,
        fullStep_fullObs c k idx s hadm hlo hI hidx hsafe.1]
      rfl

/-- Abstract output of the finite checker. -/
def fullValue (c : Cfg) (k : Nat) (r : Res) : Nat :=
  ((List.range (c.len * c.rounds)).foldl
    (fun a idx => fullGstep c k idx a) (fullObs (fullEntry c r))).residue.viol

/-- **Whole-program denotation.**  A successful finite safety certificate
connects the compiled checker all the way to the transparent joint fold. -/
theorem fullProgram_denote (c : Cfg) (k : Nat) (r : Res)
    (hadm : Admissible c) (hlo : 0 < c.lo)
    (hsafe : SafeRun c k (List.range (c.len * c.rounds)) (fullEntry c r)) :
    (fullProgram c k r).denote = some (fullValue c k r) := by
  have hmem : ∀ i ∈ List.range (c.len * c.rounds),
      i < c.len * c.rounds := fun i hi => List.mem_range.mp hi
  have hrun := safeRun_denote c k hlo hadm
    (List.range (c.len * c.rounds)) (fullEntry c r)
    hmem (fullEntry_inv c r) hsafe
  have hobs := safeRun_fullObs c k hlo hadm
    (List.range (c.len * c.rounds)) (fullEntry c r)
    hmem (fullEntry_inv c r) hsafe
  unfold Program.denote fullProgram
  simp only
  rw [fullEntry_init c r]
  change (List.foldlM
    (fun s idx => denoteInstrs idx s (fullBody c k))
    (fullEntry c r) (List.range (c.len * c.rounds))).bind
      (fun s => (denoteInstrs 0 s []).bind (fun s => some (s 104))) = _
  rw [hrun]
  simp only [denoteInstrs, Option.bind_some]
  change some ((fullObs
    ((List.range (c.len * c.rounds)).foldl
      (fun s idx => fullStep c k idx s) (fullEntry c r))).residue.viol) = _
  rw [hobs]
  rfl

end LeanCompCert.Ports.MobiusResidueTrial

import LeanCompCert.Ports.PsiRuntimeHead
import LeanCompCert.Ports.PsiRuntimePrimePackSemantics

set_option linter.unusedSimpArgs false

/-!
# Source semantics of the compiled psi head fold

The head program visits a fixed `(prime-rank, exponent-round)` grid.  This
module proves the literal body in small instruction stages so elaboration is
bounded independently of the production table size.  Production prime lists
and production-sized folds remain opaque to Lean.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

def psiHeadRank (index : Nat) : Nat := index / ppPowerRounds
def psiHeadRound (index : Nat) : Nat := index % ppPowerRounds

def psiHeadNextQ (root p q index : Nat) : Nat :=
  if psiHeadRound index = 0 then p
  else if q ≤ root / p then q * p else root + 1

def psiHeadLive (root p q index : Nat) : Nat :=
  if psiHeadNextQ root p q index ≤ root then 1 else 0

def psiHeadReadBody (m : PsiRuntimeMeta) : List AInstr :=
  (psiHeadFoldBody m).take 7

def psiHeadSelectBody (m : PsiRuntimeMeta) : List AInstr :=
  ((psiHeadFoldBody m).drop 7).take 4

def psiHeadFitBody (m : PsiRuntimeMeta) : List AInstr :=
  ((psiHeadFoldBody m).drop 11).take 7

def psiHeadQCommitBody (m : PsiRuntimeMeta) : List AInstr :=
  ((psiHeadFoldBody m).drop 18).take 3

def psiHeadLiveBody (m : PsiRuntimeMeta) : List AInstr :=
  ((psiHeadFoldBody m).drop 21).take 2

def psiHeadAccumulatorBody (m : PsiRuntimeMeta) : List AInstr :=
  (psiHeadFoldBody m).drop 23

def psiHeadFoldControlBody (m : PsiRuntimeMeta) : List AInstr :=
  (psiHeadFoldBody m).take 23

theorem psiHeadFoldBody_eq_stages (m : PsiRuntimeMeta) :
    psiHeadFoldBody m =
      psiHeadReadBody m ++ psiHeadSelectBody m ++ psiHeadFitBody m ++
        psiHeadQCommitBody m ++ psiHeadLiveBody m ++
          psiHeadAccumulatorBody m := by
  rfl

theorem psiHeadFoldControlBody_eq_stages (m : PsiRuntimeMeta) :
    psiHeadFoldControlBody m =
      psiHeadReadBody m ++ psiHeadSelectBody m ++ psiHeadFitBody m ++
        psiHeadQCommitBody m ++ psiHeadLiveBody m := by
  rfl

theorem psiHeadFoldBody_eq_control_accumulator (m : PsiRuntimeMeta) :
    psiHeadFoldBody m =
      psiHeadFoldControlBody m ++ psiHeadAccumulatorBody m := by
  rfl

private theorem psiHeadReadBody_run (m : PsiRuntimeMeta) (index : Nat)
    (s : AState) (p weight : Nat)
    (hIndexM : index < M)
    (hPrimeAddr : psiHeadRank index + m.cfg.primeBase < M)
    (hWeightAddr : psiHeadRank index + m.markBase < M)
    (hp : s.arr (m.cfg.primeBase + psiHeadRank index) = p)
    (hweight : s.arr (m.markBase + psiHeadRank index) = weight) :
    let out := arun index s (psiHeadReadBody m)
    out.regs 10 = psiHeadRank index ∧
      out.regs 11 = psiHeadRound index ∧
      out.regs 12 = (if psiHeadRound index = 0 then 1 else 0) ∧
      out.regs 14 = p ∧ out.regs 16 = weight := by
  have hIndexMod : index % M = index := Nat.mod_eq_of_lt hIndexM
  have hRoundsM : ppPowerRounds % M = ppPowerRounds := by decide
  have hRounds0 : ppPowerRounds ≠ 0 := by decide
  have hRankM : psiHeadRank index < M := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hIndexM
  have hRankMod : psiHeadRank index % M = psiHeadRank index :=
    Nat.mod_eq_of_lt hRankM
  have hRankRawMod : index / ppPowerRounds % M =
      index / ppPowerRounds := by simpa [psiHeadRank] using hRankMod
  have hRoundM : psiHeadRound index < M := by
    exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hRoundMod : psiHeadRound index % M = psiHeadRound index :=
    Nat.mod_eq_of_lt hRoundM
  have hRoundRawMod : index % ppPowerRounds % M =
      index % ppPowerRounds := by simpa [psiHeadRound] using hRoundMod
  have hPrimeAddrMod : (psiHeadRank index + m.cfg.primeBase) % M =
      psiHeadRank index + m.cfg.primeBase := Nat.mod_eq_of_lt hPrimeAddr
  have hWeightAddrMod : (psiHeadRank index + m.markBase) % M =
      psiHeadRank index + m.markBase := Nat.mod_eq_of_lt hWeightAddr
  have hPrimeAddrRawMod : (index / ppPowerRounds + m.cfg.primeBase) % M =
      index / ppPowerRounds + m.cfg.primeBase := by
    simpa [psiHeadRank] using hPrimeAddrMod
  have hWeightAddrRawMod : (index / ppPowerRounds + m.markBase) % M =
      index / ppPowerRounds + m.markBase := by
    simpa [psiHeadRank] using hWeightAddrMod
  have hpRaw : s.arr (index / ppPowerRounds + m.cfg.primeBase) = p := by
    simpa [psiHeadRank, Nat.add_comm] using hp
  have hweightRaw : s.arr (index / ppPowerRounds + m.markBase) = weight := by
    simpa [psiHeadRank, Nat.add_comm] using hweight
  simp [psiHeadReadBody, psiHeadFoldBody, psiHeadRank, psiHeadRound,
    arun, astep, sval, sdest, denoteOperand, denoteOp, AState.writeReg,
    hIndexMod, hRoundsM, hRounds0, hRankRawMod, hRoundRawMod,
    hPrimeAddrRawMod, hWeightAddrRawMod, hpRaw, hweightRaw]

private theorem psiHeadSelectBody_run (m : PsiRuntimeMeta) (index : Nat)
    (s : AState) (p q : Nat)
    (hfirst : s.regs 12 = (if psiHeadRound index = 0 then 1 else 0))
    (hp : s.regs 14 = p) (hq : s.regs headQ = q)
    (hpM : p < M) (hqM : q < M) :
    let out := arun index s (psiHeadSelectBody m)
    out.regs 17 = (if psiHeadRound index = 0 then 0 else 1) ∧
      out.regs 18 = (if psiHeadRound index = 0 then p else 0) ∧
      out.regs 20 = (if psiHeadRound index = 0 then p else q) := by
  have hOneM : (1 : Nat) % M = 1 := by decide
  have hPredM : (M - 1) % M = M - 1 := Nat.mod_eq_of_lt (by omega)
  have hMsum : 1 + (M - 1) = M := by omega
  have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
  have hqMod : q % M = q := Nat.mod_eq_of_lt hqM
  have hqRaw : s.regs 364 = q := by simpa [headQ] using hq
  by_cases hf : psiHeadRound index = 0
  · simp [psiHeadSelectBody, psiHeadFoldBody, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, hfirst, hf, hp, hqRaw,
      headQ, hOneM, hPredM, hMsum, hpMod, hqMod, Nat.add_mod, Nat.mul_mod]
  · simp [psiHeadSelectBody, psiHeadFoldBody, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, hfirst, hf, hp, hqRaw,
      headQ, hOneM, hPredM, hMsum, hpMod, hqMod, Nat.add_mod, Nat.mul_mod]

private theorem psiHeadFitBody_run (m : PsiRuntimeMeta) (index : Nat)
    (s : AState) (p candidate : Nat)
    (hp : s.regs 14 = p) (hc : s.regs 20 = candidate)
    (hp0 : 0 < p) (hpM : p < M) (hcM : candidate < M)
    (hRootSuccM : m.root + 1 < M) :
    let out := arun index s (psiHeadFitBody m)
    out.regs 17 = s.regs 17 ∧ out.regs 18 = s.regs 18 ∧
      out.regs 14 = p ∧
      out.regs 27 =
        (if candidate ≤ m.root / p then candidate * p else m.root + 1) := by
  have hRootM : m.root < M := by omega
  have hRootMod : m.root % M = m.root := Nat.mod_eq_of_lt hRootM
  have hRootSuccMod : (m.root + 1) % M = m.root + 1 :=
    Nat.mod_eq_of_lt hRootSuccM
  have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
  have hcMod : candidate % M = candidate := Nat.mod_eq_of_lt hcM
  have hpNe : p ≠ 0 := by omega
  have hDivM : m.root / p < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hRootM
  have hDivMod : (m.root / p) % M = m.root / p :=
    Nat.mod_eq_of_lt hDivM
  have hOneM : (1 : Nat) % M = 1 := by decide
  have hPredM : (M - 1) % M = M - 1 := Nat.mod_eq_of_lt (by omega)
  have hMsum : 1 + (M - 1) = M := by omega
  by_cases hfit : candidate ≤ m.root / p
  · have hprod : candidate * p ≤ m.root :=
      (Nat.le_div_iff_mul_le hp0).mp hfit
    have hprodM : candidate * p < M := Nat.lt_of_le_of_lt hprod hRootM
    have hprodMod : (candidate * p) % M = candidate * p :=
      Nat.mod_eq_of_lt hprodM
    simp [psiHeadFitBody, psiHeadFoldBody, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, hp, hc, hpMod, hcMod,
      hpNe, hDivMod, hRootMod, hRootSuccMod, hfit, hprodMod, hOneM, hPredM,
      hMsum, Nat.add_mod, Nat.mul_mod]
  · simp [psiHeadFitBody, psiHeadFoldBody, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, hp, hc, hpMod, hcMod,
      hpNe, hDivMod, hRootMod, hRootSuccMod, hfit, hOneM, hPredM, hMsum,
      Nat.add_mod, Nat.mul_mod]

private theorem psiHeadQCommitBody_run (m : PsiRuntimeMeta) (index : Nat)
    (s : AState) (p q : Nat)
    (h17 : s.regs 17 = (if psiHeadRound index = 0 then 0 else 1))
    (h18 : s.regs 18 = (if psiHeadRound index = 0 then p else 0))
    (h27 : s.regs 27 =
      (if (if psiHeadRound index = 0 then p else q) ≤ m.root / p then
        (if psiHeadRound index = 0 then p else q) * p
       else m.root + 1))
    (hpM : p < M) (hqM : q < M) (hRootSuccM : m.root + 1 < M)
    (hp0 : 0 < p) :
    (arun index s (psiHeadQCommitBody m)).regs headQ =
      psiHeadNextQ m.root p q index := by
  have hpMod : p % M = p := Nat.mod_eq_of_lt hpM
  have hqMod : q % M = q := Nat.mod_eq_of_lt hqM
  have hRootM : m.root < M := by omega
  have hRootSuccMod : (m.root + 1) % M = m.root + 1 :=
    Nat.mod_eq_of_lt hRootSuccM
  by_cases hfirst : psiHeadRound index = 0
  · simp [psiHeadQCommitBody, psiHeadFoldBody, psiHeadNextQ, arun, astep,
      sval, sdest, denoteOperand, denoteOp, AState.writeReg, headQ,
      h17, h18, h27, hfirst, hpMod, hqMod, hRootSuccMod]
  · by_cases hfit : q ≤ m.root / p
    · have hprod : q * p ≤ m.root :=
        (Nat.le_div_iff_mul_le hp0).mp hfit
      have hprodM : q * p < M := Nat.lt_of_le_of_lt hprod hRootM
      have hprodMod : (q * p) % M = q * p := Nat.mod_eq_of_lt hprodM
      simp [psiHeadQCommitBody, psiHeadFoldBody, psiHeadNextQ, arun, astep,
        sval, sdest, denoteOperand, denoteOp, AState.writeReg, headQ,
        h17, h18, h27, hfirst, hfit, hpMod, hqMod, hprodMod,
        hRootSuccMod]
    · simp [psiHeadQCommitBody, psiHeadFoldBody, psiHeadNextQ, arun, astep,
        sval, sdest, denoteOperand, denoteOp, AState.writeReg, headQ,
        h17, h18, h27, hfirst, hfit, hpMod, hqMod, hRootSuccMod]

private theorem psiHeadLiveBody_run (m : PsiRuntimeMeta) (index : Nat)
    (s : AState) (next weight : Nat)
    (hq : s.regs headQ = next) (hweight : s.regs 16 = weight)
    (hnextM : next < M) (hweightM : weight < M) (hRootM : m.root < M) :
    let out := arun index s (psiHeadLiveBody m)
    out.regs 30 = (if next ≤ m.root then 1 else 0) ∧
      out.regs 31 = (if next ≤ m.root then 1 else 0) * weight := by
  have hqRaw : s.regs 364 = next := by simpa [headQ] using hq
  have hnextMod : next % M = next := Nat.mod_eq_of_lt hnextM
  have hweightMod : weight % M = weight := Nat.mod_eq_of_lt hweightM
  have hRootMod : m.root % M = m.root := Nat.mod_eq_of_lt hRootM
  by_cases hlive : next ≤ m.root
  · simp [psiHeadLiveBody, psiHeadFoldBody, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, headQ, hqRaw, hweight,
      hnextMod, hweightMod, hRootMod, hlive]
  · simp [psiHeadLiveBody, psiHeadFoldBody, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, headQ, hqRaw, hweight,
      hnextMod, hweightMod, hRootMod, hlive]

/-- Exact source meaning of the compiled table read, guarded prime-power
advance, and live logarithm selection.  This is symbolic in the table size
and does not evaluate a prime list or a production fold in Lean. -/
theorem psiHeadFoldControl_run (m : PsiRuntimeMeta) (index : Nat)
    (s : AState) (p weight q : Nat)
    (hIndexM : index < M)
    (hRootSuccM : m.root + 1 < M)
    (hPrimeAddr : psiHeadRank index + m.cfg.primeBase < M)
    (hWeightAddr : psiHeadRank index + m.markBase < M)
    (hp : s.arr (m.cfg.primeBase + psiHeadRank index) = p)
    (hweight : s.arr (m.markBase + psiHeadRank index) = weight)
    (hq : s.regs headQ = q)
    (hp2 : 2 ≤ p) (hpRoot : p ≤ m.root)
    (hqBound : q ≤ m.root + 1)
    (hweightM : weight < M) :
    let out := arun index s (psiHeadFoldControlBody m)
    out.regs headQ = psiHeadNextQ m.root p q index ∧
      out.regs 30 = psiHeadLive m.root p q index ∧
      out.regs 31 = psiHeadLive m.root p q index * weight := by
  have hRootM : m.root < M := by omega
  have hpM : p < M := by omega
  have hqM : q < M := by omega
  have hp0 : 0 < p := by omega
  let candidate := if psiHeadRound index = 0 then p else q
  have hcM : candidate < M := by
    dsimp [candidate]
    split <;> assumption
  have hnextM : psiHeadNextQ m.root p q index < M := by
    unfold psiHeadNextQ
    split
    · exact hpM
    · split
      · rename_i hfit
        have hprod : q * p ≤ m.root :=
          (Nat.le_div_iff_mul_le hp0).mp hfit
        omega
      · exact hRootSuccM
  let sr := arun index s (psiHeadReadBody m)
  have hr := psiHeadReadBody_run m index s p weight hIndexM
    hPrimeAddr hWeightAddr hp hweight
  have srQ : sr.regs headQ = q := by
    calc
      sr.regs headQ = s.regs headQ :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index headQ
          (psiHeadReadBody m) (by rfl) s
      _ = q := hq
  let ss := arun index sr (psiHeadSelectBody m)
  have hs := psiHeadSelectBody_run m index sr p q hr.2.2.1 hr.2.2.2.1
    srQ hpM hqM
  have ss14 : ss.regs 14 = p := by
    calc
      ss.regs 14 = sr.regs 14 :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index 14
          (psiHeadSelectBody m) (by rfl) sr
      _ = p := hr.2.2.2.1
  let sf := arun index ss (psiHeadFitBody m)
  have hf := psiHeadFitBody_run m index ss p candidate ss14 (by
    simpa only [candidate] using hs.2.2) hp0 hpM hcM hRootSuccM
  let sq := arun index sf (psiHeadQCommitBody m)
  have hqout := psiHeadQCommitBody_run m index sf p q
    (hf.1.trans hs.1) (hf.2.1.trans hs.2.1) (by
      simpa only [candidate] using hf.2.2.2) hpM hqM hRootSuccM hp0
  have sr16 : sr.regs 16 = weight := hr.2.2.2.2
  have ss16 : ss.regs 16 = weight := by
    calc
      ss.regs 16 = sr.regs 16 :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index 16
          (psiHeadSelectBody m) (by rfl) sr
      _ = weight := sr16
  have sf16 : sf.regs 16 = weight := by
    calc
      sf.regs 16 = ss.regs 16 :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index 16
          (psiHeadFitBody m) (by rfl) ss
      _ = weight := ss16
  have sq16 : sq.regs 16 = weight := by
    calc
      sq.regs 16 = sf.regs 16 :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index 16
          (psiHeadQCommitBody m) (by rfl) sf
      _ = weight := sf16
  let sl := arun index sq (psiHeadLiveBody m)
  have hl := psiHeadLiveBody_run m index sq
    (psiHeadNextQ m.root p q index) weight hqout sq16 hnextM hweightM
    hRootM
  change
    (arun index s (psiHeadFoldControlBody m)).regs headQ = _ ∧
      (arun index s (psiHeadFoldControlBody m)).regs 30 = _ ∧
      (arun index s (psiHeadFoldControlBody m)).regs 31 = _
  rw [psiHeadFoldControlBody_eq_stages, arun_append, arun_append,
    arun_append, arun_append]
  exact ⟨hqout, by simpa [psiHeadLive] using hl⟩

/-- Literal modular effect of the five compiled accumulator instructions. -/
theorem psiHeadAccumulatorBody_run (m : PsiRuntimeMeta) (index : Nat)
    (s : AState) (dlo dhi term terms live : Nat)
    (hlo : s.regs rDlo = dlo) (hhi : s.regs rDhi = dhi)
    (hterm : s.regs 31 = term) (hlive : s.regs 30 = live)
    (hterms : s.regs rTerms = terms) :
    let out := arun index s (psiHeadAccumulatorBody m)
    out.regs rDlo = (dlo + term) % M ∧
      out.regs rDhi =
        (dhi + (if (dlo + term) % M < dlo then 1 else 0)) % M ∧
      out.regs rTerms = (terms + live) % M := by
  have hloRaw : s.regs 180 = dlo := by simpa [rDlo] using hlo
  have hhiRaw : s.regs 181 = dhi := by simpa [rDhi] using hhi
  have htermsRaw : s.regs 184 = terms := by simpa [rTerms] using hterms
  simp [psiHeadAccumulatorBody, psiHeadFoldBody, arun, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, rDlo, rDhi, rTerms,
    hloRaw, hhiRaw, hterm, hlive, htermsRaw]

/-- One complete compiled head-grid round: exact prime-power selection followed
by the literal two-limb and term-count updates. -/
theorem psiHeadFoldBody_run (m : PsiRuntimeMeta) (index : Nat)
    (s : AState) (p weight q dlo dhi terms : Nat)
    (hIndexM : index < M)
    (hRootSuccM : m.root + 1 < M)
    (hPrimeAddr : psiHeadRank index + m.cfg.primeBase < M)
    (hWeightAddr : psiHeadRank index + m.markBase < M)
    (hp : s.arr (m.cfg.primeBase + psiHeadRank index) = p)
    (hweight : s.arr (m.markBase + psiHeadRank index) = weight)
    (hq : s.regs headQ = q)
    (hlo : s.regs rDlo = dlo) (hhi : s.regs rDhi = dhi)
    (hterms : s.regs rTerms = terms)
    (hp2 : 2 ≤ p) (hpRoot : p ≤ m.root)
    (hqBound : q ≤ m.root + 1)
    (hweightM : weight < M) :
    let next := psiHeadNextQ m.root p q index
    let live := psiHeadLive m.root p q index
    let term := live * weight
    let out := arun index s (psiHeadFoldBody m)
    out.regs headQ = next ∧
      out.regs rDlo = (dlo + term) % M ∧
      out.regs rDhi =
        (dhi + (if (dlo + term) % M < dlo then 1 else 0)) % M ∧
      out.regs rTerms = (terms + live) % M := by
  let sc := arun index s (psiHeadFoldControlBody m)
  have hc := psiHeadFoldControl_run m index s p weight q hIndexM
    hRootSuccM hPrimeAddr hWeightAddr hp hweight hq hp2 hpRoot hqBound
    hweightM
  have scLo : sc.regs rDlo = dlo := by
    calc
      sc.regs rDlo = s.regs rDlo :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index rDlo
          (psiHeadFoldControlBody m) (by rfl) s
      _ = dlo := hlo
  have scHi : sc.regs rDhi = dhi := by
    calc
      sc.regs rDhi = s.regs rDhi :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index rDhi
          (psiHeadFoldControlBody m) (by rfl) s
      _ = dhi := hhi
  have scTerms : sc.regs rTerms = terms := by
    calc
      sc.regs rTerms = s.regs rTerms :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index rTerms
          (psiHeadFoldControlBody m) (by rfl) s
      _ = terms := hterms
  have ha := psiHeadAccumulatorBody_run m index sc dlo dhi
    (psiHeadLive m.root p q index * weight) terms
    (psiHeadLive m.root p q index) scLo scHi hc.2.2 hc.2.1 scTerms
  have houtQ :
      (arun index sc (psiHeadAccumulatorBody m)).regs headQ =
        psiHeadNextQ m.root p q index := by
    calc
      (arun index sc (psiHeadAccumulatorBody m)).regs headQ =
          sc.regs headQ :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index headQ
          (psiHeadAccumulatorBody m) (by rfl) sc
      _ = psiHeadNextQ m.root p q index := hc.1
  dsimp only
  rw [psiHeadFoldBody_eq_control_accumulator, arun_append]
  exact ⟨houtQ, ha⟩

#print axioms psiHeadReadBody_run
#print axioms psiHeadSelectBody_run
#print axioms psiHeadFitBody_run
#print axioms psiHeadQCommitBody_run
#print axioms psiHeadLiveBody_run
#print axioms psiHeadFoldControl_run
#print axioms psiHeadAccumulatorBody_run
#print axioms psiHeadFoldBody_run

end LeanCompCert.Ports.PsiSegSieve

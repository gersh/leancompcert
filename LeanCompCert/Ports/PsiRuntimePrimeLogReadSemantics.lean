import LeanCompCert.Ports.PsiRuntimePrimeLogCoreSemantics

/-!
# Loop-index and resident-table reads in the compiled psi log producer

The literal prefix decodes a flat loop index into `(prime rank, log round)`,
sets first/final flags, and reads the resident prime and exponent tables.
The proofs remain symbolic in every table entry and in the production size.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

def psiPrimeLogScale (m : PsiRuntimeMeta) : Nat := max 1 m.cfg.sc
def psiPrimeLogRank (m : PsiRuntimeMeta) (index : Nat) : Nat :=
  index / psiPrimeLogScale m
def psiPrimeLogRoundIndex (m : PsiRuntimeMeta) (index : Nat) : Nat :=
  index % psiPrimeLogScale m

def psiPrimeLogDecodeBody (m : PsiRuntimeMeta) : List AInstr :=
  (psiPrimeLogBody m).take 2

def psiPrimeLogFlagsBody (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 2).take 3

def psiPrimeLogTableBody (m : PsiRuntimeMeta) : List AInstr :=
  ((psiPrimeLogBody m).drop 5).take 4

def psiPrimeLogReadBody (m : PsiRuntimeMeta) : List AInstr :=
  (psiPrimeLogBody m).take 9

theorem psiPrimeLogReadBody_eq_stages (m : PsiRuntimeMeta) :
    psiPrimeLogReadBody m =
      psiPrimeLogDecodeBody m ++ psiPrimeLogFlagsBody m ++
        psiPrimeLogTableBody m := by rfl

private theorem psiPrimeLogDecodeBody_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState)
    (hIndexM : index < M) (hScaleM : psiPrimeLogScale m < M) :
    let out := arun index s (psiPrimeLogDecodeBody m)
    out.regs 10 = psiPrimeLogRank m index ∧
      out.regs 11 = psiPrimeLogRoundIndex m index ∧ out.arr = s.arr := by
  have hIndexMod : index % M = index := Nat.mod_eq_of_lt hIndexM
  have hScale0 : psiPrimeLogScale m ≠ 0 := by
    simp [psiPrimeLogScale]
  have hScalePos : 0 < psiPrimeLogScale m := by omega
  have hScaleMod : psiPrimeLogScale m % M = psiPrimeLogScale m :=
    Nat.mod_eq_of_lt hScaleM
  have hRankM : psiPrimeLogRank m index < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hIndexM
  have hRoundM : psiPrimeLogRoundIndex m index < M :=
    Nat.lt_trans (Nat.mod_lt _ hScalePos) hScaleM
  have hScaleExprMod : max 1 m.cfg.sc % M = max 1 m.cfg.sc := by
    simpa only [psiPrimeLogScale] using hScaleMod
  have hRankExprMod : index / max 1 m.cfg.sc % M =
      index / max 1 m.cfg.sc := by
    simpa only [psiPrimeLogRank, psiPrimeLogScale] using
      (Nat.mod_eq_of_lt hRankM)
  have hRoundExprMod : index % max 1 m.cfg.sc % M =
      index % max 1 m.cfg.sc := by
    simpa only [psiPrimeLogRoundIndex, psiPrimeLogScale] using
      (Nat.mod_eq_of_lt hRoundM)
  simp [psiPrimeLogDecodeBody, psiPrimeLogBody, psiPrimeLogRank,
    psiPrimeLogRoundIndex, psiPrimeLogScale, arun, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, hIndexMod, hScaleExprMod,
    hRankExprMod, hRoundExprMod]

private theorem psiPrimeLogFlagsBody_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (j : Nat)
    (hj : s.regs 11 = j) (hjlt : j < psiPrimeLogScale m)
    (hsc : 0 < m.cfg.sc) (hscM : m.cfg.sc < M) :
    let out := arun index s (psiPrimeLogFlagsBody m)
    out.regs 12 = (if j = 0 then 1 else 0) ∧
      out.regs 14 = (if j + 1 = m.cfg.sc then 1 else 0) ∧
      out.arr = s.arr := by
  have hScaleEq : psiPrimeLogScale m = m.cfg.sc := by
    exact Nat.max_eq_right (by omega)
  have hsuccM : (j + 1) % M = j + 1 := Nat.mod_eq_of_lt (by omega)
  have hscMod : m.cfg.sc % M = m.cfg.sc := Nat.mod_eq_of_lt hscM
  have hOneMod : (1 : Nat) % M = 1 := by decide
  by_cases hj0 : j = 0 <;> by_cases hfin : j + 1 = m.cfg.sc <;>
    simp [psiPrimeLogFlagsBody, psiPrimeLogBody, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, hj, hsuccM, hscMod,
      hj0, hfin, hOneMod]

private theorem psiPrimeLogTableBody_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState)
    (rank p e : Nat) (hrank : s.regs 10 = rank)
    (hPrimeAddr : rank + m.cfg.primeBase < M)
    (hMarkAddr : rank + m.markBase < M)
    (hp : s.arr (m.cfg.primeBase + rank) = p)
    (he : s.arr (m.markBase + rank) = e) :
    let out := arun index s (psiPrimeLogTableBody m)
    out.regs 16 = p ∧ out.regs 17 = rank + m.markBase ∧
      out.regs 18 = e ∧ out.arr = s.arr := by
  have hPrimeMod : (rank + m.cfg.primeBase) % M =
      rank + m.cfg.primeBase := Nat.mod_eq_of_lt hPrimeAddr
  have hMarkMod : (rank + m.markBase) % M = rank + m.markBase :=
    Nat.mod_eq_of_lt hMarkAddr
  have hp' : s.arr (rank + m.cfg.primeBase) = p := by
    simpa [Nat.add_comm] using hp
  have he' : s.arr (rank + m.markBase) = e := by
    simpa [Nat.add_comm] using he
  simp [psiPrimeLogTableBody, psiPrimeLogBody, arun, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, hrank, hPrimeMod, hMarkMod,
    hp', he']

/-- Exact source meaning of the literal nine-instruction read prefix. -/
theorem psiPrimeLogReadBody_run
    (m : PsiRuntimeMeta) (index : Nat) (s : AState) (p e : Nat)
    (hIndexM : index < M) (hsc : 0 < m.cfg.sc) (hscM : m.cfg.sc < M)
    (hPrimeAddr : psiPrimeLogRank m index + m.cfg.primeBase < M)
    (hMarkAddr : psiPrimeLogRank m index + m.markBase < M)
    (hp : s.arr (m.cfg.primeBase + psiPrimeLogRank m index) = p)
    (he : s.arr (m.markBase + psiPrimeLogRank m index) = e) :
    let out := arun index s (psiPrimeLogReadBody m)
    out.regs 10 = psiPrimeLogRank m index ∧
      out.regs 11 = psiPrimeLogRoundIndex m index ∧
      out.regs 12 =
        (if psiPrimeLogRoundIndex m index = 0 then 1 else 0) ∧
      out.regs 14 =
        (if psiPrimeLogRoundIndex m index + 1 = m.cfg.sc then 1 else 0) ∧
      out.regs 16 = p ∧
      out.regs 17 = psiPrimeLogRank m index + m.markBase ∧
      out.regs 18 = e ∧ out.arr = s.arr := by
  let decoded := arun index s (psiPrimeLogDecodeBody m)
  have hScaleEq : psiPrimeLogScale m = m.cfg.sc := by
    exact Nat.max_eq_right (by omega)
  have hScaleM : psiPrimeLogScale m < M := by simpa [hScaleEq] using hscM
  have hd := psiPrimeLogDecodeBody_run m index s hIndexM hScaleM
  have hjlt : psiPrimeLogRoundIndex m index < psiPrimeLogScale m :=
    Nat.mod_lt _ (by
      show 0 < max 1 m.cfg.sc
      omega)
  let flagged := arun index decoded (psiPrimeLogFlagsBody m)
  have hf := psiPrimeLogFlagsBody_run m index decoded
    (psiPrimeLogRoundIndex m index) hd.2.1 hjlt hsc hscM
  have hRankFrame : flagged.regs 10 = psiPrimeLogRank m index := by
    calc
      flagged.regs 10 = decoded.regs 10 :=
        LeanCompCert.Verified.ArrayRegFrame.arun_frame index 10
          (psiPrimeLogFlagsBody m) (by rfl) decoded
      _ = psiPrimeLogRank m index := hd.1
  have ht := psiPrimeLogTableBody_run m index flagged
    (psiPrimeLogRank m index) p e hRankFrame hPrimeAddr hMarkAddr
    (by rw [hf.2.2, hd.2.2]; exact hp)
    (by rw [hf.2.2, hd.2.2]; exact he)
  rw [psiPrimeLogReadBody_eq_stages, arun_append, arun_append]
  exact ⟨by simpa [flagged, decoded] using
      (LeanCompCert.Verified.ArrayRegFrame.arun_frame index 10
        (psiPrimeLogTableBody m) (by rfl) flagged).trans hRankFrame,
    by simpa [flagged, decoded] using
      (LeanCompCert.Verified.ArrayRegFrame.arun_frame index 11
        (psiPrimeLogTableBody m) (by rfl) flagged).trans
          ((LeanCompCert.Verified.ArrayRegFrame.arun_frame index 11
            (psiPrimeLogFlagsBody m) (by rfl) decoded).trans hd.2.1),
    by simpa [flagged, decoded] using
      (LeanCompCert.Verified.ArrayRegFrame.arun_frame index 12
        (psiPrimeLogTableBody m) (by rfl) flagged).trans hf.1,
    by simpa [flagged, decoded] using
      (LeanCompCert.Verified.ArrayRegFrame.arun_frame index 14
        (psiPrimeLogTableBody m) (by rfl) flagged).trans hf.2.1,
    ht.1, ht.2.1, ht.2.2.1,
    ht.2.2.2.trans (hf.2.2.trans hd.2.2)⟩

#print axioms psiPrimeLogReadBody_run

end LeanCompCert.Ports.PsiSegSieve

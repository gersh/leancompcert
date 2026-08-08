import LeanCompCert.Ports.MobiusSquaredResidueModel
import LeanCompCert.Ports.ArraySegMobiusResidueFold

/-!
# The production squared residue denotes its transparent model

The old five-section prefix is kept opaque and is read through its existing
small-block theorems.  The new 71-instruction suffix is read through
`testBody_arun_source_spec`.  This avoids elaborating the 113-instruction
state transformer as one term.
-/

namespace LeanCompCert.Ports.MobiusSquaredResidueRealisation

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusSquaredSound
open LeanCompCert.Ports.MobiusResidueRealisation

/-- The unchanged production prefix, split at the old section boundaries. -/
def squaredPrefix (k : Nat) : List AInstr :=
  blkA k ++ (blkB ++ (blkC k ++ (blkD ++ blkE)))

theorem mobiusLiveSquaredResidue_eq_prefix (k : Nat) :
    mobiusLiveSquaredResidue k = squaredPrefix k ++ mobiusSquaredTestBody k := by
  rfl

private theorem blockA_arun (k len idx : Nat) (s : AState)
    (hn : s.regs 65 ≠ 0) :
    denoteAInstrs len idx s (blkA k) = some (arun idx s (blkA k)) := by
  obtain ⟨out, hout⟩ := blkA_ok k len idx s hn
  have heq := eq_arun_of_denoteAInstrs_eq_some len idx (blkA k) s out hout
  simpa only [heq] using hout

private theorem blockB_arun (len idx : Nat) (s : AState) :
    denoteAInstrs len idx s blkB = some (arun idx s blkB) := by
  obtain ⟨out, hout⟩ := blkB_ok len idx s
  have heq := eq_arun_of_denoteAInstrs_eq_some len idx blkB s out hout
  simpa only [heq] using hout

private theorem blockC_arun (k len idx : Nat) (s : AState) :
    denoteAInstrs len idx s (blkC k) = some (arun idx s (blkC k)) := by
  obtain ⟨out, hout⟩ := blkC_ok k len idx s
  have heq := eq_arun_of_denoteAInstrs_eq_some len idx (blkC k) s out hout
  simpa only [heq] using hout

private theorem blockD_arun (len idx : Nat) (s : AState) :
    denoteAInstrs len idx s blkD = some (arun idx s blkD) := by
  obtain ⟨out, hout⟩ := blkD_ok len idx s
  have heq := eq_arun_of_denoteAInstrs_eq_some len idx blkD s out hout
  simpa only [heq] using hout

private theorem blockE_arun (len idx : Nat) (s : AState) :
    denoteAInstrs len idx s blkE = some (arun idx s blkE) := by
  obtain ⟨out, hout⟩ := blkE_ok len idx s
  have heq := eq_arun_of_denoteAInstrs_eq_some len idx blkE s out hout
  simpa only [heq] using hout

private theorem denoteAInstrs_append_intro (len idx : Nat) (s sm out : AState)
    (xs ys : List AInstr)
    (hx : denoteAInstrs len idx s xs = some sm)
    (hy : denoteAInstrs len idx sm ys = some out) :
    denoteAInstrs len idx s (xs ++ ys) = some out := by
  rw [denoteAInstrs_append, hx]
  exact hy

set_option maxRecDepth 100000 in
/-- The complete squared residue has a successful partial denotation whenever
its candidate register is nonzero.  This is the source-definedness theorem
needed by whole-program compiler certificates: the unchanged prefix contains
the only divisions, all by register `65`, while the squared suffix is a
division-free scalar block and therefore cannot fail or access the array. -/
theorem mobiusLiveSquaredResidue_denote_arun (k len idx : Nat) (s : AState)
    (hn : s.regs 65 ≠ 0) :
    denoteAInstrs len idx s (mobiusLiveSquaredResidue k) =
      some (arun idx s (mobiusLiveSquaredResidue k)) := by
  let sA := arun idx s (blkA k)
  let sB := arun idx sA blkB
  let sC := arun idx sB (blkC k)
  let sD := arun idx sC blkD
  let sE := arun idx sD blkE
  have hA := blockA_arun k len idx s hn
  have hB := blockB_arun len idx sA
  have hC := blockC_arun k len idx sB
  have hD := blockD_arun len idx sC
  have hE := blockE_arun len idx sD
  have hDE : denoteAInstrs len idx sC (blkD ++ blkE) = some sE :=
    denoteAInstrs_append_intro len idx sC sD sE blkD blkE hD hE
  have hCDE : denoteAInstrs len idx sB
      (blkC k ++ (blkD ++ blkE)) = some sE :=
    denoteAInstrs_append_intro len idx sB sC sE (blkC k)
      (blkD ++ blkE) hC hDE
  have hBCDE : denoteAInstrs len idx sA
      (blkB ++ (blkC k ++ (blkD ++ blkE))) = some sE :=
    denoteAInstrs_append_intro len idx sA sB sE blkB
      (blkC k ++ (blkD ++ blkE)) hB hCDE
  have hprefix :
      denoteAInstrs len idx s (squaredPrefix k) = some sE := by
    rw [squaredPrefix]
    exact denoteAInstrs_append_intro len idx s sA sE (blkA k)
      (blkB ++ (blkC k ++ (blkD ++ blkE))) hA hBCDE
  have hprefixArun : arun idx s (squaredPrefix k) = sE := by
    simp only [squaredPrefix, arun_append]
    rfl
  have htestDef : AllDefined len idx sE (mobiusSquaredTestBody k) := by
    rw [test_lift]
    exact allDefined_lift_of_noDiv len idx (testG k) sE (by rfl)
  have htest : denoteAInstrs len idx sE (mobiusSquaredTestBody k) =
      some (arun idx sE (mobiusSquaredTestBody k)) :=
    denoteAInstrs_eq_arun len idx (mobiusSquaredTestBody k) sE htestDef
  have hrun : arun idx s (mobiusLiveSquaredResidue k) =
      arun idx sE (mobiusSquaredTestBody k) := by
    rw [mobiusLiveSquaredResidue_eq_prefix, arun_append, hprefixArun]
  rw [hrun, mobiusLiveSquaredResidue_eq_prefix]
  exact denoteAInstrs_append_intro len idx s sE
    (arun idx sE (mobiusSquaredTestBody k)) (squaredPrefix k)
    (mobiusSquaredTestBody k) hprefix htest

/-- The unchanged prefix exposes exactly the inputs and persistent outputs
needed by the squared suffix. -/
theorem squaredPrefix_arun_spec (k len idx : Nat) (s : AState)
    (hn : s.regs 65 ≠ 0) :
    let p := arun idx s (squaredPrefix k)
    let w := wPair k (s.regs 65)
    let t := accStep (s.regs 79) (s.regs 80) w.1 w.2
      (s.regs rTLo) (s.regs rTHi)
    let a := absBias (vBias k t.1 t.2)
    let c := celStep (s.regs 65) (s.regs rCeilSq) (s.regs rCeil)
      (s.regs 133)
    p.regs rTLo = t.1 ∧ p.regs rTHi = t.2 ∧
      p.regs rCeil = c.1 ∧ p.regs rCeilSq = c.2 ∧
      p.regs rMViol = s.regs rMViol ∧ p.regs 159 = a ∧
      p.regs 65 = s.regs 65 ∧ p.regs 133 = s.regs 133 := by
  let sA := arun idx s (blkA k)
  let sB := arun idx sA blkB
  let sC := arun idx sB (blkC k)
  let sD := arun idx sC blkD
  let sE := arun idx sD blkE
  have hA := blockA_arun k len idx s hn
  have hB := blockB_arun len idx sA
  have hC := blockC_arun k len idx sB
  have hD := blockD_arun len idx sC
  have hE := blockE_arun len idx sD
  have fA (j : Nat) (hj : (blkA k).all (avoidsReg j) = true) :
      sA.regs j = s.regs j := arun_reg_frame idx j (blkA k) s hj
  have fB (j : Nat) (hj : blkB.all (avoidsReg j) = true) :
      sB.regs j = sA.regs j := arun_reg_frame idx j blkB sA hj
  have fC (j : Nat) (hj : (blkC k).all (avoidsReg j) = true) :
      sC.regs j = sB.regs j := arun_reg_frame idx j (blkC k) sB hj
  have fD (j : Nat) (hj : blkD.all (avoidsReg j) = true) :
      sD.regs j = sC.regs j := arun_reg_frame idx j blkD sC hj
  have fE (j : Nat) (hj : blkE.all (avoidsReg j) = true) :
      sE.regs j = sD.regs j := arun_reg_frame idx j blkE sD hj
  have hAwl := blkA_wl k len idx s hn hA
  have hAwh := blkA_wh k len idx s hn hA
  have hBt : sB.regs 100 =
      (accStep (s.regs 79) (s.regs 80) (wPair k (s.regs 65)).1
        (wPair k (s.regs 65)).2 (s.regs 100) (s.regs 101)).1 := by
    rw [blkB_tLo k len idx sA hB,
      fA 79 (by rfl), fA 80 (by rfl), hAwl, hAwh,
      fA 100 (by rfl), fA 101 (by rfl)]
  have hBh : sB.regs 101 =
      (accStep (s.regs 79) (s.regs 80) (wPair k (s.regs 65)).1
        (wPair k (s.regs 65)).2 (s.regs 100) (s.regs 101)).2 := by
    rw [blkB_tHi k len idx sA hB,
      fA 79 (by rfl), fA 80 (by rfl), hAwl, hAwh,
      fA 100 (by rfl), fA 101 (by rfl)]
  have hCv : sC.regs 152 = vBias k (sB.regs 100) (sB.regs 101) :=
    blkC_v k len idx sB hC
  have hDa : sD.regs 159 = absBias (vBias k (sB.regs 100) (sB.regs 101)) := by
    rw [blkD_abs k len idx sC hD, hCv]
  have hEc : sE.regs 102 =
      (celStep (s.regs 65) (s.regs 103) (s.regs 102)
        (s.regs 133)).1 := by
    rw [blkE_cel k len idx sD hE,
      fD 65 (by rfl), fC 65 (by rfl), fB 65 (by rfl), fA 65 (by rfl),
      fD 103 (by rfl), fC 103 (by rfl), fB 103 (by rfl),
      fA 103 (by rfl), fD 102 (by rfl), fC 102 (by rfl),
      fB 102 (by rfl), fA 102 (by rfl), fD 133 (by rfl),
      fC 133 (by rfl), fB 133 (by rfl), fA 133 (by rfl)]
  have hEcSq : sE.regs 103 =
      (celStep (s.regs 65) (s.regs 103) (s.regs 102)
        (s.regs 133)).2 := by
    rw [blkE_celSq k len idx sD hE,
      fD 65 (by rfl), fC 65 (by rfl), fB 65 (by rfl), fA 65 (by rfl),
      fD 103 (by rfl), fC 103 (by rfl), fB 103 (by rfl),
      fA 103 (by rfl), fD 102 (by rfl), fC 102 (by rfl),
      fB 102 (by rfl), fA 102 (by rfl), fD 133 (by rfl),
      fC 133 (by rfl), fB 133 (by rfl), fA 133 (by rfl)]
  have hp : arun idx s (squaredPrefix k) = sE := by
    simp only [squaredPrefix, arun_append]
    rfl
  rw [hp]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [rTLo, rTHi] using (show sE.regs 100 = _ by
      rw [fE 100 (by rfl), fD 100 (by rfl), fC 100 (by rfl), hBt])
  · simpa only [rTLo, rTHi] using (show sE.regs 101 = _ by
      rw [fE 101 (by rfl), fD 101 (by rfl), fC 101 (by rfl), hBh])
  · simpa only [rCeil, rCeilSq] using hEc
  · simpa only [rCeil, rCeilSq] using hEcSq
  · rw [fE rMViol (by rfl), fD rMViol (by rfl), fC rMViol (by rfl),
      fB rMViol (by rfl), fA rMViol (by rfl)]
  · rw [fE 159 (by rfl), hDa, hBt, hBh]
    simp only [rTLo, rTHi]
  · rw [fE 65 (by rfl), fD 65 (by rfl), fC 65 (by rfl),
      fB 65 (by rfl), fA 65 (by rfl)]
  · rw [fE 133 (by rfl), fD 133 (by rfl), fC 133 (by rfl),
      fB 133 (by rfl), fA 133 (by rfl)]

/-- The absolute-value word produced by section (D) is at most `2^63`.
This is a format fact, independent of the accumulator invariant. -/
theorem absBias_le_two_pow_63 (v : Nat) (hv : v < M) :
    absBias v ≤ 2 ^ 63 := by
  rw [absBias_spec v hv]
  have hM : M = 2 ^ 64 := rfl
  rw [hM] at hv
  split <;> omega

/-- A campaign endpoint below `2^62` gives both no-wrap facts needed by the
division-free squared suffix.  This deliberately uses only the word format
and the public `k ≤ 15` range, so idle and marking events need no separate
accumulator estimate. -/
theorem squaredResidue_word_bounds (k n pos neg tLo tHi : Nat)
    (hk : k ≤ 15) (hn : n < 2 ^ 62) :
    n + 2 ^ (k + 2) < M ∧
      (let w := wPair k n
       let t := accStep pos neg w.1 w.2 tLo tHi
       let a := absBias (vBias k t.1 t.2)
       a + (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 < M) := by
  have hp : 2 ^ (k + 2) ≤ 2 ^ 17 := by
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hM : M = 2 ^ 64 := rfl
  have hnwrap : n + 2 ^ (k + 2) < M := by
    rw [hM]
    omega
  refine ⟨hnwrap, ?_⟩
  dsimp only
  let t := accStep pos neg (wPair k n).1 (wPair k n).2 tLo tHi
  have hv : vBias k t.1 t.2 < M := by
    unfold vBias
    exact Nat.mod_lt _ (by rw [hM]; omega)
  have ha : absBias (vBias k t.1 t.2) ≤ 2 ^ 63 :=
    absBias_le_two_pow_63 _ hv
  have hq : (n + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) ≤
      n + 2 ^ (k + 2) - 1 := Nat.div_le_self _ _
  dsimp only [t] at ha ⊢
  rw [hM]
  omega

/-- One actual 113-instruction residue execution is exactly one transparent
squared step.  The guards are the sole partial division and the explicit
word/no-wrap bounds of the root-free suffix. -/
theorem readRes_arun_squaredResidue (k len idx : Nat) (s : AState)
    (hregs : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hn0 : s.regs 65 ≠ 0) (hk : k ≤ 15)
    (hn : s.regs 65 + 2 ^ (k + 2) < M)
    (hu : let w := wPair k (s.regs 65)
      let t := accStep (s.regs 79) (s.regs 80) w.1 w.2
        (s.regs rTLo) (s.regs rTHi)
      let a := absBias (vBias k t.1 t.2)
      a + (s.regs 65 + 2 ^ (k + 2) - 1) / 2 ^ (k + 2) + 1 < M) :
    readRes (arun idx s (mobiusLiveSquaredResidue k)) =
      squaredResStep k (readSig s) (readRes s) := by
  let p := arun idx s (squaredPrefix k)
  have hp := squaredPrefix_arun_spec k len idx s hn0
  have hpword : ∀ j, p.regs j < M :=
    arun_regs_word idx (squaredPrefix k) s hregs harr
  have hp65 : p.regs 65 = s.regs 65 := hp.2.2.2.2.2.2.1
  have hp159 : p.regs 159 =
      absBias (vBias k
        (accStep (s.regs 79) (s.regs 80) (wPair k (s.regs 65)).1
          (wPair k (s.regs 65)).2 (s.regs rTLo) (s.regs rTHi)).1
        (accStep (s.regs 79) (s.regs 80) (wPair k (s.regs 65)).1
          (wPair k (s.regs 65)).2 (s.regs rTLo) (s.regs rTHi)).2) :=
    hp.2.2.2.2.2.1
  have hp133 : p.regs 133 = s.regs 133 := hp.2.2.2.2.2.2.2
  have htest := testBody_arun_source_spec idx k p hpword hk
    (by simpa only [hp65] using hn) (by
      simpa only [hp65, hp159] using hu)
  rw [mobiusLiveSquaredResidue_eq_prefix, arun_append]
  unfold readRes readSig squaredResStep squaredViolStep SquaredPass squaredUpper
  dsimp only
  simp only [Res.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [arun_reg_frame idx rTLo (mobiusSquaredTestBody k) p (by rfl), hp.1]
  · rw [arun_reg_frame idx rTHi (mobiusSquaredTestBody k) p (by rfl), hp.2.1]
  · rw [arun_reg_frame idx rCeil (mobiusSquaredTestBody k) p (by rfl), hp.2.2.1]
  · rw [arun_reg_frame idx rCeilSq (mobiusSquaredTestBody k) p (by rfl),
      hp.2.2.2.1]
  · rw [htest, hp.2.2.2.2.1, hp65, hp159, hp133]

end LeanCompCert.Ports.MobiusSquaredResidueRealisation

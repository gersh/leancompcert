import LeanCompCert.Ports.PsiFixedCheck

/-!
# The ψ fixed-point check: one round, assembled

`Ports/PsiFixedCheck.lean` defines the program and proves what each straight
block computes.  This file finishes the machine half: the F-round spec, the
staged composition (`psRun_spec`), definedness of the body, and
`psProgram_denote` — the register program's denotation is the flat fold of
`psRound`.

Nothing here is a certificate, nothing here asserts that any execution
happened, and nothing here adds an axiom.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace LeanCompCert.Ports.PsiFixedCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.Frontend
open LeanCompCert.Verified.Straight
open LeanCompCert.Ports.TrialDivisionFold (sel divStep)

private theorem lit0 : (0 : Nat) % M = 0 := by decide
private theorem lit1 : (1 : Nat) % M = 1 := by decide
private theorem lit2 : (2 : Nat) % M = 2 := by decide
private theorem litSC : SC % M = SC := by decide
private theorem litSC1 : (SC - 1) % M = SC - 1 := by decide
private theorem litCAP : CAP % M = CAP := by decide
private theorem lit27 : (134217728 : Nat) % M = 134217728 := by decide
private theorem litL2C : L2C % M = L2C := by decide
private theorem two24_lt_M : (2 : Nat) ^ 24 < M := by decide

/-- `a − b` computed in `u64`, for `b ≤ a < 2⁶⁴`. -/
private theorem subM (a b : Nat) (hba : b ≤ a) (ha : a < M) :
    (a + (M - b)) % M = a - b := by
  have hb : b < M := Nat.lt_of_le_of_lt hba ha
  rw [show a + (M - b) = M + (a - b) by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (show a - b < M by omega)]

/-! ### The F round, in three stages

One straight block whose later assignments re-read earlier destinations
duplicates the earlier expression tree at every read; six chained assignments
make that duplication exponential, and the kernel then walks the proof term as
a tree.  Splitting at the two high-fanout registers (`46`, `47`/`0`) keeps
every stage's tree small.  `blkF2_eq` re-joins the stages by `rfl`.
-/

/-- The λ term. -/
def blkF2a : List Assign :=
  [ ⟨46, .bin .mul (.reg 8) (.bin .add (.bin .mul (.lit L2C) (.reg 5)) (.reg 10))⟩ ]

/-- The accumulator add, its wrap guard, and the accumulator move. -/
def blkF2b : List Assign :=
  [ ⟨47, .bin .add (.reg 0) (.bin .mul (.reg 22) (.reg 46))⟩
  , ⟨2, .bin .mul (.reg 2) (.bin .ge (.reg 47) (.reg 0))⟩
  , ⟨0, .reg 47⟩ ]

/-- The masked slope test. -/
def blkF2c (P : Params) : List Assign :=
  [ ⟨48, .bin .bor (.bin .le (.reg 0) (.bin .mul (.reg 14) (.lit P.K)))
      (.bin .lt (.reg 14) (.lit P.lo))⟩
  , ⟨1, .bin .mul (.reg 1) (.bin .bor (.reg 48) (.bin .bxor (.reg 22) (.lit 1)))⟩ ]

theorem blkF2_eq (P : Params) : blkF2 P = blkF2a ++ (blkF2b ++ blkF2c P) := rfl

/-- Stage a: the λ term. -/
theorem blkF2a_spec (k : Nat) (t : RegState) (pp e1 sum3 : Nat)
    (h8 : t 8 = pp) (h5 : t 5 = e1) (h10 : t 10 = sum3)
    (hpp : pp ≤ 1) (he1 : e1 ≤ 32) (hsum3 : sum3 ≤ CAP) :
    run k t blkF2a 46 = pp * (L2C * e1 + sum3) := by
  have hL2C : L2C < 2 ^ 28 := by decide
  have he1M : e1 < M := by
    have := two24_lt_M
    omega
  have heLM : L2C * e1 < M := by
    have h1 : L2C * e1 ≤ L2C * 32 := Nat.mul_le_mul_left _ he1
    have h2 : L2C * 32 < M := by decide
    omega
  have hlamIn : L2C * e1 + sum3 < M := by
    have h1 : L2C * e1 ≤ L2C * 32 := Nat.mul_le_mul_left _ he1
    have h2 : L2C * 32 + CAP < M := by decide
    omega
  have hlam : pp * (L2C * e1 + sum3) < M := by
    have : pp * (L2C * e1 + sum3) ≤ L2C * e1 + sum3 := by
      rcases (show pp = 0 ∨ pp = 1 by omega) with h | h <;> simp [h]
    omega
  have hppM : pp < M := by
    have := two24_lt_M
    omega
  simp [run, blkF2a, evalExpr, denoteOp, RegState.set, h8, h5, h10, litL2C,
    Nat.mod_eq_of_lt he1M, Nat.mod_eq_of_lt heLM, Nat.mod_eq_of_lt hlamIn,
    Nat.mod_eq_of_lt hlam, Nat.mod_eq_of_lt hppM]

/-- Stage b: the guarded accumulator step. -/
theorem blkF2b_spec (k : Nat) (t : RegState) (acc0 isF lam ok2 : Nat)
    (h0 : t 0 = acc0) (h22 : t 22 = isF) (h46 : t 46 = lam) (h2 : t 2 = ok2)
    (hacc0 : acc0 < M) (hisF : isF ≤ 1) (hlamM : lam < M) (hok2 : ok2 ≤ 1) :
    run k t blkF2b 0 = (acc0 + isF * lam) % M ∧
    run k t blkF2b 2 =
      ok2 * (if acc0 ≤ (acc0 + isF * lam) % M then 1 else 0) ∧
    run k t blkF2b 14 = t 14 ∧ run k t blkF2b 1 = t 1 ∧
    run k t blkF2b 22 = isF := by
  have hifl : isF * lam < M := by
    have : isF * lam ≤ lam := by
      rcases (show isF = 0 ∨ isF = 1 by omega) with h | h <;> simp [h]
    omega
  have hok2M : ok2 < M := by
    have : (1 : Nat) < M := by decide
    omega
  have hokifM :
      ok2 * (if acc0 ≤ (acc0 + isF * lam) % M then (1 : Nat) else 0) < M := by
    have h1 : (if acc0 ≤ (acc0 + isF * lam) % M then (1 : Nat) else 0) ≤ 1 := by
      split <;> omega
    have h2 : ok2 * (if acc0 ≤ (acc0 + isF * lam) % M then (1 : Nat) else 0)
        ≤ 1 * 1 := Nat.mul_le_mul hok2 h1
    have : (1 : Nat) < M := by decide
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [run, blkF2b, evalExpr, denoteOp, RegState.set, h0, h22, h46, h2,
      ge_iff_le, Nat.mod_eq_of_lt hifl, Nat.mod_eq_of_lt hok2M,
      Nat.mod_eq_of_lt hokifM, Nat.mod_eq_of_lt hacc0]

/-- Stage c: the masked slope test. -/
theorem blkF2c_spec (P : Params) (k : Nat) (t : RegState)
    (acc1 n isF pass0 : Nat)
    (h0 : t 0 = acc1) (h14 : t 14 = n) (h22 : t 22 = isF) (h1 : t 1 = pass0)
    (hacc1 : acc1 < M) (hn : n ≤ 2 ^ 24) (hisF : isF ≤ 1) (hpass0 : pass0 ≤ 1)
    (hKM : P.K % M = P.K) (hloM : P.lo % M = P.lo) (hK : P.K < 2 ^ 30) :
    run k t (blkF2c P) 1 =
      pass0 *
        (((if acc1 ≤ n * P.K then 1 else 0) ||| (if n < P.lo then 1 else 0))
          ||| isF ^^^ 1) ∧
    run k t (blkF2c P) 0 = acc1 ∧ run k t (blkF2c P) 2 = t 2 := by
  have hnK : n * P.K < M := by
    have h1 : n * P.K ≤ 2 ^ 24 * P.K := Nat.mul_le_mul_right _ hn
    have h2 : (2 : Nat) ^ 24 * P.K ≤ 2 ^ 24 * 2 ^ 30 :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt hK)
    have h3 : (2 : Nat) ^ 24 * 2 ^ 30 < M := by decide
    omega
  have hnM : n < M := by
    have := two24_lt_M
    omega
  have hpassM : pass0 < M := by
    have : (1 : Nat) < M := by decide
    omega
  have hor01 : ∀ (p q : Prop) (_ : Decidable p) (_ : Decidable q),
      ((if p then (1 : Nat) else 0) ||| (if q then 1 else 0)) % M =
        (if p then 1 else 0) ||| (if q then 1 else 0) := by
    intro p q i1 i2
    split <;> split <;> decide
  have hAB1 : ∀ (p q : Prop) (_ : Decidable p) (_ : Decidable q),
      (((if p then (1 : Nat) else 0) ||| (if q then 1 else 0)) ||| 1) = 1 := by
    intro p q i1 i2
    split <;> split <;> decide
  have hmulor : ∀ (p q : Prop) (_ : Decidable p) (_ : Decidable q),
      (pass0 * ((if p then (1 : Nat) else 0) ||| (if q then 1 else 0))) % M =
        pass0 * ((if p then 1 else 0) ||| (if q then 1 else 0)) := by
    intro p q i1 i2
    split <;> split <;> simp [Nat.mod_eq_of_lt hpassM]
  rcases (show isF = 0 ∨ isF = 1 by omega) with hF | hF <;> subst hF <;>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [run, blkF2c, evalExpr, denoteOp, RegState.set, h0, h14, h22, h1,
        lit1, hKM, hloM, hor01, hAB1, hmulor, Nat.mod_eq_of_lt hnK,
        Nat.mod_eq_of_lt hnM, Nat.mod_eq_of_lt hpassM,
        Nat.mod_eq_of_lt hacc1]

/-! ## Untouched-register lemmas -/

private theorem regSet_ne (u : RegState) (i v j : Nat) (h : j ≠ i) :
    (u.set i v) j = u j := by simp [RegState.set, h]

private theorem divStep_ne (dest : Nat) (op : Op) (a b j : Nat) (t : RegState)
    (h : j ≠ dest) : divStep dest op a b t j = t j := by
  simp [divStep, RegState.set, h]

private theorem divLitStep_ne (dest : Nat) (op : Op) (a c j : Nat)
    (t : RegState) (h : j ≠ dest) : divLitStep dest op a c t j = t j := by
  simp [divLitStep, RegState.set, h]

private theorem blkA_unt (P : Params) (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([16, 17, 18, 19, 20, 21, 22, 23, 14, 15, 3, 4, 5, 6, 7, 8, 9,
      10, 11, 24] : List Nat)) :
    run k t (blkA P) r = t r := by
  refine run_untouched k (blkA P) r ?_ t
  intro a ha
  simp only [blkA, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkB_unt (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([26, 27, 3, 4, 28, 29, 5, 6, 30] : List Nat)) :
    run k t blkB r = t r := by
  refine run_untouched k blkB r ?_ t
  intro a ha
  simp only [blkB, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkB1_unt (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([26, 27, 3, 4] : List Nat)) :
    run k t blkB1 r = t r := by
  refine run_untouched k blkB1 r ?_ t
  intro a ha
  simp only [blkB1, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkB2_unt (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([28, 29, 5, 6, 30] : List Nat)) :
    run k t blkB2 r = t r := by
  refine run_untouched k blkB2 r ?_ t
  intro a ha
  simp only [blkB2, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkC_unt (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([7, 8, 32, 33] : List Nat)) :
    run k t blkC r = t r := by
  refine run_untouched k blkC r ?_ t
  intro a ha
  simp only [blkC, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkD_unt (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([35, 2, 36, 11, 9, 10, 37] : List Nat)) :
    run k t blkD r = t r := by
  refine run_untouched k blkD r ?_ t
  intro a ha
  simp only [blkD, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkE_unt (P : Params) (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([39, 40] : List Nat)) :
    run k t (blkE P) r = t r := by
  refine run_untouched k (blkE P) r ?_ t
  intro a ha
  simp only [blkE, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkF1_unt (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([9, 42, 43, 44, 2, 45, 10] : List Nat)) :
    run k t blkF1 r = t r := by
  refine run_untouched k blkF1 r ?_ t
  intro a ha
  simp only [blkF1, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkF2a_unt (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([46] : List Nat)) :
    run k t blkF2a r = t r := by
  refine run_untouched k blkF2a r ?_ t
  intro a ha
  simp only [blkF2a, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkF2b_unt (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([47, 2, 0] : List Nat)) :
    run k t blkF2b r = t r := by
  refine run_untouched k blkF2b r ?_ t
  intro a ha
  simp only [blkF2b, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

private theorem blkF2c_unt (P : Params) (k : Nat) (t : RegState) (r : Nat)
    (hr : ¬ r ∈ ([48, 1] : List Nat)) :
    run k t (blkF2c P) r = t r := by
  refine run_untouched k (blkF2c P) r ?_ t
  intro a ha
  simp only [blkF2c, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl|rfl <;>
    (intro heq; exact hr (by subst heq; simp))

/-! ## §R1 Small arithmetic helpers -/

private theorem pow2_le_24 {a b : Nat} (h1 : 2 ^ a ≤ b) (h2 : b ≤ 2 ^ 24) :
    a ≤ 24 := by
  rcases Nat.lt_or_ge a 25 with h | h
  · omega
  · exfalso
    have h3 : (2 : Nat) ^ 25 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) h
    have h4 : (2 : Nat) ^ 24 < 2 ^ 25 := by decide
    omega

private theorem tq_le_SC {t1 xh1 : Nat} (ht : t1 ≤ SC) (hx : xh1 ≤ 2 ^ 27) :
    ((SC - 1) + t1 * xh1) / SC ≤ SC := by
  have hSC0 : 0 < SC := by decide
  have hnum : (SC - 1) + t1 * xh1 < (2 ^ 27 + 1) * SC := by
    have h1 : t1 * xh1 ≤ SC * 2 ^ 27 := by
      have := Nat.mul_le_mul ht hx
      omega
    have h2 : (2 ^ 27 + 1) * SC = 2 ^ 27 * SC + SC := Nat.succ_mul _ _
    have h3 : SC * 2 ^ 27 = 2 ^ 27 * SC := Nat.mul_comm _ _
    omega
  have := (Nat.div_lt_iff_lt_mul hSC0).mpr hnum
  have h27 : (2 : Nat) ^ 27 + 1 ≤ SC := by decide
  omega

private theorem term_le_tq {tq dv : Nat} (hdv : 1 ≤ dv) :
    (tq + (dv - 1)) / dv ≤ tq := by
  have hnum : tq + (dv - 1) < (tq + 1) * dv := by
    have h1 : tq ≤ tq * dv := Nat.le_mul_of_pos_right tq (by omega)
    have h2 : (tq + 1) * dv = tq * dv + dv := Nat.succ_mul _ _
    omega
  have := (Nat.div_lt_iff_lt_mul (by omega : 0 < dv)).mpr hnum
  omega

/-! ## §R2 `psRound`, with its intermediate values named -/

theorem psRound_mk (P : Params) (k : Nat) (v : Vals)
    (rr n d isT isE isX isS isMv isL isF
      p0 fnd0 e0 pw0 pow0 pp0 t0 sum0 xh0 pb hit p1 fnd1
      tw2 cE e1 pw1 pr pow1 pp1 xn1 xq gX ok1 xcap xh1 t1 sum1
      tq dv term t2 scn sum2 gS ok2 scap sum3 lam acc1 ok3 chk pass1 : Nat)
    (err : rr = k % P.R) (en : n = P.start + k / P.R) (ed : d = rr + 2)
    (eisT : isT = if rr < P.td then 1 else 0)
    (eisE : isE =
      (if P.td ≤ rr then 1 else 0) * (if rr < P.td + 24 then 1 else 0))
    (eisX : isX = if rr = P.td + 24 then 1 else 0)
    (eisS : isS =
      (if P.td + 25 ≤ rr then 1 else 0) * (if rr < P.td + 66 then 1 else 0))
    (eisMv : isMv =
      (if P.td + 25 ≤ rr then 1 else 0) * (if rr < P.td + 65 then 1 else 0))
    (eisL : isL = if rr = P.td + 65 then 1 else 0)
    (eisF : isF = if rr = P.td + 66 then 1 else 0)
    (ep0 : p0 = if rr = 0 then 1 else v.p)
    (efnd0 : fnd0 = if rr = 0 then 0 else v.fnd)
    (ee0 : e0 = if rr = 0 then 0 else v.e)
    (epw0 : pw0 = if rr = 0 then 1 else v.pw)
    (epow0 : pow0 = if rr = 0 then 1 else v.pow)
    (epp0 : pp0 = if rr = 0 then 0 else v.pp)
    (et0 : t0 = if rr = 0 then 0 else v.t)
    (esum0 : sum0 = if rr = 0 then 0 else v.sum)
    (exh0 : xh0 = if rr = 0 then 0 else v.xh)
    (epb : pb = if fnd0 = 1 then p0 else n)
    (ehit : hit = if n % d = 0 then 1 else 0)
    (ep1 : p1 = if isT * (fnd0 ^^^ 1) * hit = 1 then d else p0)
    (efnd1 : fnd1 = (fnd0 ||| isT * hit))
    (etw2 : tw2 = pw0 * 2)
    (ecE : cE = isE * (if tw2 ≤ pb then 1 else 0))
    (ee1 : e1 = e0 + cE)
    (epw1 : pw1 = if cE = 1 then tw2 else pw0)
    (epr : pr = pow0 * pb % n)
    (epow1 : pow1 = if isE = 1 then pr else pow0)
    (epp1 : pp1 = (pp0 ||| isE * (if pr = 0 then 1 else 0)))
    (exn1 : xn1 = (if pw1 ≤ pb then 1 else 0) * (pb - pw1))
    (exq : xq = (SC * xn1 + (pb - 1)) / pb)
    (egX : gX = if xq ≤ 2 ^ 27 then 1 else 0)
    (eok1 : ok1 = v.ok * (gX ||| isX ^^^ 1))
    (excap : xcap = if gX = 1 then xq else 2 ^ 27)
    (exh1 : xh1 = if isX = 1 then xcap else xh0)
    (et1 : t1 = if isX = 1 then SC else t0)
    (esum1 : sum1 = if isX = 1 then 0 else sum0)
    (etq : tq = ((SC - 1) + t1 * xh1) / SC)
    (edv : dv = if isMv = 1 then rr - (P.td + 24) else 1)
    (eterm : term = (tq + (dv - 1)) / dv)
    (et2 : t2 = if isS = 1 then tq else t1)
    (escn : scn = isMv * term + isL * (2 * tq))
    (esum2 : sum2 = sum1 + scn)
    (egS : gS = if sum2 ≤ CAP then 1 else 0)
    (eok2 : ok2 = ok1 * (gS ||| isS ^^^ 1))
    (escap : scap = if gS = 1 then sum2 else CAP)
    (esum3 : sum3 = if isS = 1 then scap else sum1)
    (elam : lam = pp1 * (L2C * e1 + sum3))
    (eacc1 : acc1 = (v.acc + isF * lam) % M)
    (eok3 : ok3 = ok2 * (if v.acc ≤ acc1 then 1 else 0))
    (echk : chk =
      ((if acc1 ≤ n * P.K then 1 else 0) ||| (if n < P.lo then 1 else 0)))
    (epass1 : pass1 = v.pass * (chk ||| isF ^^^ 1)) :
    psRound P k v =
      { acc := acc1, pass := pass1, ok := ok3, p := p1, fnd := fnd1, e := e1,
        pw := pw1, pow := pow1, pp := pp1, t := t2, sum := sum3, xh := xh1 } := by
  subst err en ed eisT eisE eisX eisS eisMv eisL eisF ep0 efnd0 ee0 epw0 epow0
    epp0 et0 esum0 exh0 epb ehit ep1 efnd1 etw2 ecE ee1 epw1 epr epow1 epp1
    exn1 exq egX eok1 excap exh1 et1 esum1 etq edv eterm et2 escn esum2 egS
    eok2 escap esum3 elam eacc1 eok3 echk epass1
  rfl

/-! ## §R2b Every register the round writes stays a word -/

private theorem divStep_lt (dest : Nat) (op : Op) (a b : Nat) (s : RegState)
    (hs : ∀ i, s i < M) : ∀ i, divStep dest op a b s i < M := by
  intro i
  by_cases h : i = dest
  · subst h
    show (if i = i then (denoteOp op (s a) (s b)).getD 0 else s i) < M
    rw [if_pos rfl]
    cases hd : denoteOp op (s a) (s b) with
    | none => exact M_pos
    | some r => exact denoteOp_lt op _ _ r hd
  · show (if i = dest then (denoteOp op (s a) (s b)).getD 0 else s i) < M
    rw [if_neg h]
    exact hs i

private theorem divLitStep_lt (dest : Nat) (op : Op) (a c : Nat) (s : RegState)
    (hs : ∀ i, s i < M) : ∀ i, divLitStep dest op a c s i < M := by
  intro i
  by_cases h : i = dest
  · subst h
    show (if i = i then (denoteOp op (s a) (c % M)).getD 0 else s i) < M
    rw [if_pos rfl]
    cases hd : denoteOp op (s a) (c % M) with
    | none => exact M_pos
    | some r => exact denoteOp_lt op _ _ r hd
  · show (if i = dest then (denoteOp op (s a) (c % M)).getD 0 else s i) < M
    rw [if_neg h]
    exact hs i

private theorem idxStep_lt (R k : Nat) (s : RegState) (hs : ∀ i, s i < M) :
    ∀ i, idxStep R k s i < M := by
  intro i
  show (if i = 13 then (denoteOp .udiv (k % M) (R % M)).getD 0
    else (if i = 12 then (denoteOp .urem (k % M) (R % M)).getD 0 else s i)) < M
  by_cases h13 : i = 13
  · rw [if_pos h13]
    cases hd : denoteOp Op.udiv (k % M) (R % M) with
    | none => exact M_pos
    | some r => exact denoteOp_lt _ _ _ r hd
  · rw [if_neg h13]
    by_cases h12 : i = 12
    · rw [if_pos h12]
      cases hd : denoteOp Op.urem (k % M) (R % M) with
      | none => exact M_pos
      | some r => exact denoteOp_lt _ _ _ r hd
    · rw [if_neg h12]
      exact hs i

theorem psRun_lt (P : Params) (k : Nat) (s : RegState) (hs : ∀ i, s i < M) :
    ∀ i, psRun P k s i < M := by
  show ∀ i, run k (st11 P k s) (blkF P) i < M
  refine run_lt k cursor (blkF P) (blkF_wf P) _ ?_
  show ∀ i, divStep 41 .udiv 40 39 (st10 P k s) i < M
  refine divStep_lt _ _ _ _ _ ?_
  show ∀ i, run k (st9 P k s) (blkE P) i < M
  refine run_lt k cursor (blkE P) (blkE_wf P) _ ?_
  show ∀ i, divLitStep 38 .udiv 37 SC (st8 P k s) i < M
  refine divLitStep_lt _ _ _ _ _ ?_
  show ∀ i, run k (st7 P k s) blkD i < M
  refine run_lt k cursor blkD blkD_wf _ ?_
  show ∀ i, divStep 34 .udiv 33 24 (st6 P k s) i < M
  refine divStep_lt _ _ _ _ _ ?_
  show ∀ i, run k (st5 P k s) blkC i < M
  refine run_lt k cursor blkC blkC_wf _ ?_
  show ∀ i, divStep 31 .urem 30 14 (st4 P k s) i < M
  refine divStep_lt _ _ _ _ _ ?_
  show ∀ i, run k (st3 P k s) blkB i < M
  refine run_lt k cursor blkB blkB_wf _ ?_
  show ∀ i, divStep 25 .urem 14 15 (st2 P k s) i < M
  refine divStep_lt _ _ _ _ _ ?_
  show ∀ i, run k (st1 P k s) (blkA P) i < M
  refine run_lt k cursor (blkA P) (blkA_wf P) _ ?_
  exact idxStep_lt P.R k s hs

private theorem or_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a ||| b) ≤ 1 := by
  rcases (show a = 0 ∨ a = 1 by omega) with h | h <;>
    rcases (show b = 0 ∨ b = 1 by omega) with h' | h' <;>
      subst h <;> subst h' <;> decide

private theorem mul_le_one' {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b ≤ 1 := by
  rcases (show a = 0 ∨ a = 1 by omega) with h | h <;>
    rcases (show b = 0 ∨ b = 1 by omega) with h' | h' <;>
      subst h <;> subst h' <;> decide

/-! ## §R3 One round, under the invariant -/

section Round

variable {P : Params} {k : Nat} {s : RegState}

private theorem idx12 {P : Params} {k : Nat} {s : RegState}
    (hP : P.Sane) (hk : k < P.fuel * P.R) :
    st1 P k s 12 = k % P.R := by
  have hne : P.R ≠ 0 := by have := hP.RPos; omega
  have h : k % P.R < M :=
    Nat.lt_trans (Nat.mod_lt _ hP.RPos) hP.RLtM
  simp [st1, idxStep, RegState.set, denoteOp, hP.RModM,
    Nat.mod_eq_of_lt (hP.loopLtM hk), hne, Nat.mod_eq_of_lt h]

private theorem idx13 {P : Params} {k : Nat} {s : RegState}
    (hP : P.Sane) (hk : k < P.fuel * P.R) :
    st1 P k s 13 = k / P.R := by
  have hne : P.R ≠ 0 := by have := hP.RPos; omega
  simp [st1, idxStep, RegState.set, denoteOp, hP.RModM,
    Nat.mod_eq_of_lt (hP.loopLtM hk), hne,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self k P.R)
      (hP.loopLtM hk))]

private theorem idxOther {P : Params} {k : Nat} {s : RegState} (j : Nat)
    (h12 : j ≠ 12) (h13 : j ≠ 13) : st1 P k s j = s j := by
  simp [st1, idxStep, RegState.set, h12, h13]

private theorem bit01 (p : Prop) [Decidable p] :
    (if p then (1 : Nat) else 0) = 0 ∨ (if p then (1 : Nat) else 0) = 1 := by
  split <;> simp

private theorem bitmul01 (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then (1 : Nat) else 0) * (if q then 1 else 0)) = 0 ∨
      ((if p then (1 : Nat) else 0) * (if q then 1 else 0)) = 1 := by
  split <;> split <;> simp

/--
**One round.**  At an index the loop actually visits, and in a state
satisfying the invariant, the four register divisors are live, the twelve
carried registers of `psRun` are exactly `psRound`, and the invariant is
preserved.
-/
theorem psRun_spec (hP : P.Sane) (hk : k < P.fuel * P.R) (hs : PSInv P s) :
    st2 P k s 15 ≠ 0 ∧ st4 P k s 14 ≠ 0 ∧ st6 P k s 24 ≠ 0 ∧
      st10 P k s 39 ≠ 0 ∧
      valsOf (psRun P k s) = psRound P k (valsOf s) ∧
      PSInv P (psRun P k s) := by
  have hMbig : (2 : Nat) ^ 25 < M := by decide
  have hSCM : SC < M := by decide
  have hCAPM : CAP < M := by decide
  have hT2 : P.T ≤ 2 ^ 24 := hP.topSmall
  have hT1 : 2 ≤ P.T := by
    have := hP.fuelPos
    have := hP.startPos
    show 2 ≤ P.start + P.fuel
    omega
  have hTM : P.T < M := hP.TLtM
  have hq : k / P.R < P.fuel := hP.qLt hk
  have hrrR : k % P.R < P.R := Nat.mod_lt _ hP.RPos
  have hRB : P.R ≤ 2 ^ 24 + 65 := by
    have h1 := hP.tdSmall
    have h2 := hP.topSmall
    show P.td + 67 ≤ 2 ^ 24 + 65
    omega
  -- Names for every intermediate quantity of the round.
  obtain ⟨rr, err⟩ : ∃ x, x = k % P.R := ⟨_, rfl⟩
  obtain ⟨q, eq'⟩ : ∃ x, x = k / P.R := ⟨_, rfl⟩
  obtain ⟨n, en⟩ : ∃ x, x = P.start + k / P.R := ⟨_, rfl⟩
  obtain ⟨d, ed⟩ : ∃ x, x = rr + 2 := ⟨_, rfl⟩
  obtain ⟨isT, eisT⟩ : ∃ x, x = if rr < P.td then (1 : Nat) else 0 := ⟨_, rfl⟩
  obtain ⟨isE, eisE⟩ : ∃ x, x =
    (if P.td ≤ rr then (1 : Nat) else 0) * (if rr < P.td + 24 then 1 else 0) :=
    ⟨_, rfl⟩
  obtain ⟨isX, eisX⟩ : ∃ x, x = if rr = P.td + 24 then (1 : Nat) else 0 :=
    ⟨_, rfl⟩
  obtain ⟨isS, eisS⟩ : ∃ x, x =
    (if P.td + 25 ≤ rr then (1 : Nat) else 0) *
      (if rr < P.td + 66 then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨isMv, eisMv⟩ : ∃ x, x =
    (if P.td + 25 ≤ rr then (1 : Nat) else 0) *
      (if rr < P.td + 65 then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨isL, eisL⟩ : ∃ x, x = if rr = P.td + 65 then (1 : Nat) else 0 :=
    ⟨_, rfl⟩
  obtain ⟨isF, eisF⟩ : ∃ x, x = if rr = P.td + 66 then (1 : Nat) else 0 :=
    ⟨_, rfl⟩
  obtain ⟨p0, ep0⟩ : ∃ x, x = if rr = 0 then 1 else s 3 := ⟨_, rfl⟩
  obtain ⟨fnd0, efnd0⟩ : ∃ x, x = if rr = 0 then 0 else s 4 := ⟨_, rfl⟩
  obtain ⟨e0, ee0⟩ : ∃ x, x = if rr = 0 then 0 else s 5 := ⟨_, rfl⟩
  obtain ⟨pw0, epw0⟩ : ∃ x, x = if rr = 0 then 1 else s 6 := ⟨_, rfl⟩
  obtain ⟨pow0, epow0⟩ : ∃ x, x = if rr = 0 then 1 else s 7 := ⟨_, rfl⟩
  obtain ⟨pp0, epp0⟩ : ∃ x, x = if rr = 0 then 0 else s 8 := ⟨_, rfl⟩
  obtain ⟨t0, et0⟩ : ∃ x, x = if rr = 0 then 0 else s 9 := ⟨_, rfl⟩
  obtain ⟨sum0, esum0⟩ : ∃ x, x = if rr = 0 then 0 else s 10 := ⟨_, rfl⟩
  obtain ⟨xh0, exh0⟩ : ∃ x, x = if rr = 0 then 0 else s 11 := ⟨_, rfl⟩
  obtain ⟨pb, epb⟩ : ∃ x, x = if fnd0 = 1 then p0 else n := ⟨_, rfl⟩
  obtain ⟨hit, ehit⟩ : ∃ x, x = if n % d = 0 then (1 : Nat) else 0 := ⟨_, rfl⟩
  obtain ⟨p1, ep1⟩ :
    ∃ x, x = if isT * (fnd0 ^^^ 1) * hit = 1 then d else p0 := ⟨_, rfl⟩
  obtain ⟨fnd1, efnd1⟩ : ∃ x, x = (fnd0 ||| isT * hit) := ⟨_, rfl⟩
  obtain ⟨tw2, etw2⟩ : ∃ x, x = pw0 * 2 := ⟨_, rfl⟩
  obtain ⟨cE, ecE⟩ : ∃ x, x = isE * (if tw2 ≤ pb then (1 : Nat) else 0) :=
    ⟨_, rfl⟩
  obtain ⟨e1, ee1⟩ : ∃ x, x = e0 + cE := ⟨_, rfl⟩
  obtain ⟨pw1, epw1⟩ : ∃ x, x = if cE = 1 then tw2 else pw0 := ⟨_, rfl⟩
  obtain ⟨pr, epr⟩ : ∃ x, x = pow0 * pb % n := ⟨_, rfl⟩
  obtain ⟨pow1, epow1⟩ : ∃ x, x = if isE = 1 then pr else pow0 := ⟨_, rfl⟩
  obtain ⟨pp1, epp1⟩ :
    ∃ x, x = (pp0 ||| isE * (if pr = 0 then (1 : Nat) else 0)) := ⟨_, rfl⟩
  obtain ⟨xn1, exn1⟩ :
    ∃ x, x = (if pw1 ≤ pb then (1 : Nat) else 0) * (pb - pw1) := ⟨_, rfl⟩
  obtain ⟨xq, exq⟩ : ∃ x, x = (SC * xn1 + (pb - 1)) / pb := ⟨_, rfl⟩
  obtain ⟨gX, egX⟩ : ∃ x, x = if xq ≤ 2 ^ 27 then (1 : Nat) else 0 := ⟨_, rfl⟩
  obtain ⟨ok1, eok1⟩ : ∃ x, x = s 2 * (gX ||| isX ^^^ 1) := ⟨_, rfl⟩
  obtain ⟨xcap, excap⟩ : ∃ x, x = if gX = 1 then xq else 2 ^ 27 := ⟨_, rfl⟩
  obtain ⟨xh1, exh1⟩ : ∃ x, x = if isX = 1 then xcap else xh0 := ⟨_, rfl⟩
  obtain ⟨t1, et1⟩ : ∃ x, x = if isX = 1 then SC else t0 := ⟨_, rfl⟩
  obtain ⟨sum1, esum1⟩ : ∃ x, x = if isX = 1 then 0 else sum0 := ⟨_, rfl⟩
  obtain ⟨tq, etq⟩ : ∃ x, x = ((SC - 1) + t1 * xh1) / SC := ⟨_, rfl⟩
  obtain ⟨dv, edv⟩ : ∃ x, x = if isMv = 1 then rr - (P.td + 24) else 1 :=
    ⟨_, rfl⟩
  obtain ⟨term, eterm⟩ : ∃ x, x = (tq + (dv - 1)) / dv := ⟨_, rfl⟩
  obtain ⟨t2, et2⟩ : ∃ x, x = if isS = 1 then tq else t1 := ⟨_, rfl⟩
  obtain ⟨scn, escn⟩ : ∃ x, x = isMv * term + isL * (2 * tq) := ⟨_, rfl⟩
  obtain ⟨sum2, esum2⟩ : ∃ x, x = sum1 + scn := ⟨_, rfl⟩
  obtain ⟨gS, egS⟩ : ∃ x, x = if sum2 ≤ CAP then (1 : Nat) else 0 := ⟨_, rfl⟩
  obtain ⟨ok2, eok2⟩ : ∃ x, x = ok1 * (gS ||| isS ^^^ 1) := ⟨_, rfl⟩
  obtain ⟨scap, escap⟩ : ∃ x, x = if gS = 1 then sum2 else CAP := ⟨_, rfl⟩
  obtain ⟨sum3, esum3⟩ : ∃ x, x = if isS = 1 then scap else sum1 := ⟨_, rfl⟩
  obtain ⟨lam, elam⟩ : ∃ x, x = pp1 * (L2C * e1 + sum3) := ⟨_, rfl⟩
  obtain ⟨acc1, eacc1⟩ : ∃ x, x = (s 0 + isF * lam) % M := ⟨_, rfl⟩
  obtain ⟨ok3, eok3⟩ :
    ∃ x, x = ok2 * (if s 0 ≤ acc1 then (1 : Nat) else 0) := ⟨_, rfl⟩
  obtain ⟨chk, echk⟩ : ∃ x, x =
    ((if acc1 ≤ n * P.K then (1 : Nat) else 0) |||
      (if n < P.lo then 1 else 0)) := ⟨_, rfl⟩
  obtain ⟨pass1, epass1⟩ : ∃ x, x = s 1 * (chk ||| isF ^^^ 1) := ⟨_, rfl⟩
  -- Sizes of the decoded quantities.
  have hrrB : rr < 2 ^ 25 := by
    rw [err]
    omega
  have hrrM : rr < M := by omega
  have hn1 : 1 ≤ n := by
    have := hP.startPos
    omega
  have hnT : n < P.T := by
    rw [en]
    show P.start + k / P.R < P.start + P.fuel
    omega
  have hn24 : n ≤ 2 ^ 24 := by omega
  have hnM : n < M := by omega
  have hd2 : 2 ≤ d := by omega
  have hdM : d < M := by
    have h25 : (2 : Nat) ^ 25 + 2 < M := by decide
    omega
  have hdT : rr < P.td → d ≤ P.T - 1 := by
    intro h
    have h2 := hP.tdSmall
    show d ≤ P.start + P.fuel - 1
    omega
  -- Carried-register facts, after the reset.
  have hp0pos : 1 ≤ p0 := by
    rw [ep0]; split
    · omega
    · exact hs.pPos
  have hp0T : p0 ≤ P.T := by
    rw [ep0]; split
    · omega
    · exact hs.pLe
  have hfnd0 : fnd0 ≤ 1 := by
    rw [efnd0]; split
    · omega
    · exact hs.fndLe
  have hpw0pow : pw0 = 2 ^ e0 := by
    rw [epw0, ee0]
    split
    · rfl
    · exact hs.pwPow
  have hpw0T : pw0 ≤ P.T := by
    rw [epw0]; split
    · omega
    · exact hs.pwLe
  have he024 : e0 ≤ 24 := pow2_le_24 (by rw [← hpw0pow]; exact hpw0T) hT2
  have hpow0T : pow0 ≤ P.T := by
    rw [epow0]; split
    · omega
    · exact hs.powLe
  have hpp0 : pp0 ≤ 1 := by
    rw [epp0]; split
    · omega
    · exact hs.ppLe
  have ht0SC : t0 ≤ SC := by
    rw [et0]; split
    · omega
    · exact hs.tLe
  have hsum0C : sum0 ≤ CAP := by
    rw [esum0]; split
    · omega
    · exact hs.sumLe
  have hxh027 : xh0 ≤ 2 ^ 27 := by
    rw [exh0]; split
    · omega
    · exact hs.xhLe
  have hpb1 : 1 ≤ pb := by
    rw [epb]; split
    · exact hp0pos
    · exact hn1
  have hpbT : pb ≤ P.T := by
    rw [epb]; split
    · exact hp0T
    · omega
  have hpb24 : pb ≤ 2 ^ 24 := by omega
  have hpbM : pb < M := by omega
  have hqf : q < P.fuel := by rw [eq']; exact hq
  have hqsM : q + P.start < M := by
    have : q + P.start < P.start + P.fuel := by omega
    have hTM' : P.start + P.fuel < M := hP.TLtM
    omega
  have en2 : P.start + q = n := by rw [en, eq']
  have htdM : P.td % M = P.td := Nat.mod_eq_of_lt (by
    have h1 := hP.tdSmall
    have h2 := hP.topSmall
    have := two24_lt_M
    omega)
  have htd24M : (P.td + 24) % M = P.td + 24 := Nat.mod_eq_of_lt (by
    have h1 := hP.tdSmall
    have h2 := hP.topSmall
    have h3 : (2 : Nat) ^ 24 + 24 < M := by decide
    omega)
  have htd25M : (P.td + 25) % M = P.td + 25 := Nat.mod_eq_of_lt (by
    have h1 := hP.tdSmall
    have h2 := hP.topSmall
    have h3 : (2 : Nat) ^ 24 + 25 < M := by decide
    omega)
  have htd65M : (P.td + 65) % M = P.td + 65 := Nat.mod_eq_of_lt (by
    have h1 := hP.tdSmall
    have h2 := hP.topSmall
    have h3 : (2 : Nat) ^ 24 + 65 < M := by decide
    omega)
  have htd66M : (P.td + 66) % M = P.td + 66 := Nat.mod_eq_of_lt (by
    have h1 := hP.tdSmall
    have h2 := hP.topSmall
    have h3 : (2 : Nat) ^ 24 + 66 < M := by decide
    omega)
  have hstartM : P.start % M = P.start := Nat.mod_eq_of_lt (by
    have h2 := hP.topSmall
    have := two24_lt_M
    omega)
  -- Stage 1: index decoding.
  have h12v : st1 P k s 12 = rr := by rw [err]; exact idx12 hP hk
  have h13v : st1 P k s 13 = q := by rw [eq']; exact idx13 hP hk
  -- Stage 2: the decode/reset block.
  obtain ⟨a0, a1, a2, a12, a14, a15, a16, a17, a18, a19, a20, a21, a22,
      a3, a4, a5, a6, a7, a8, a9, a10, a11, a24⟩ :=
    blkA_spec P k (st1 P k s) rr q h12v h13v htdM htd24M htd25M htd65M htd66M
      hstartM (by rw [Nat.mod_eq_of_lt hqsM]; omega)
      (by rw [en2]; exact Nat.mod_eq_of_lt (by omega))
      (by rw [← ed]; exact Nat.mod_eq_of_lt hdM)
      (by rw [idxOther 3 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 3))
      (by rw [idxOther 4 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 4))
      (by rw [idxOther 5 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 5))
      (by rw [idxOther 6 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 6))
      (by rw [idxOther 7 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 7))
      (by rw [idxOther 8 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 8))
      (by rw [idxOther 9 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 9))
      (by rw [idxOther 10 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 10))
      (by rw [idxOther 11 (by decide) (by decide)]
          exact Nat.mod_eq_of_lt (hs.word 11))
      (by rw [idxOther 4 (by decide) (by decide)]
          have := hs.fndLe
          omega)
  -- `st2` values, in the names of the round.
  have b0 : st2 P k s 0 = s 0 := by
    show run k (st1 P k s) (blkA P) 0 = s 0
    rw [a0, idxOther 0 (by decide) (by decide)]
  have b1 : st2 P k s 1 = s 1 := by
    show run k (st1 P k s) (blkA P) 1 = s 1
    rw [a1, idxOther 1 (by decide) (by decide)]
  have b2 : st2 P k s 2 = s 2 := by
    show run k (st1 P k s) (blkA P) 2 = s 2
    rw [a2, idxOther 2 (by decide) (by decide)]
  have b12 : st2 P k s 12 = rr := a12
  have b14 : st2 P k s 14 = n := by
    show run k (st1 P k s) (blkA P) 14 = n
    rw [a14, en2]
  have b15 : st2 P k s 15 = d := by
    show run k (st1 P k s) (blkA P) 15 = d
    rw [a15, ← ed]
  have b16 : st2 P k s 16 = isT := by
    show run k (st1 P k s) (blkA P) 16 = isT
    rw [a16, ← eisT]
  have b17 : st2 P k s 17 = isE := by
    show run k (st1 P k s) (blkA P) 17 = isE
    rw [a17, ← eisE]
  have b18 : st2 P k s 18 = isX := by
    show run k (st1 P k s) (blkA P) 18 = isX
    rw [a18, ← eisX]
  have b19 : st2 P k s 19 = isS := by
    show run k (st1 P k s) (blkA P) 19 = isS
    rw [a19, ← eisS]
  have b20 : st2 P k s 20 = isMv := by
    show run k (st1 P k s) (blkA P) 20 = isMv
    rw [a20, ← eisMv]
  have b21 : st2 P k s 21 = isL := by
    show run k (st1 P k s) (blkA P) 21 = isL
    rw [a21, ← eisL]
  have b22 : st2 P k s 22 = isF := by
    show run k (st1 P k s) (blkA P) 22 = isF
    rw [a22, ← eisF]
  have b3 : st2 P k s 3 = p0 := by
    show run k (st1 P k s) (blkA P) 3 = p0
    rw [a3, idxOther 3 (by decide) (by decide), ← ep0]
  have b4 : st2 P k s 4 = fnd0 := by
    show run k (st1 P k s) (blkA P) 4 = fnd0
    rw [a4, idxOther 4 (by decide) (by decide), ← efnd0]
  have b5 : st2 P k s 5 = e0 := by
    show run k (st1 P k s) (blkA P) 5 = e0
    rw [a5, idxOther 5 (by decide) (by decide), ← ee0]
  have b6 : st2 P k s 6 = pw0 := by
    show run k (st1 P k s) (blkA P) 6 = pw0
    rw [a6, idxOther 6 (by decide) (by decide), ← epw0]
  have b7 : st2 P k s 7 = pow0 := by
    show run k (st1 P k s) (blkA P) 7 = pow0
    rw [a7, idxOther 7 (by decide) (by decide), ← epow0]
  have b8 : st2 P k s 8 = pp0 := by
    show run k (st1 P k s) (blkA P) 8 = pp0
    rw [a8, idxOther 8 (by decide) (by decide), ← epp0]
  have b9 : st2 P k s 9 = t0 := by
    show run k (st1 P k s) (blkA P) 9 = t0
    rw [a9, idxOther 9 (by decide) (by decide), ← et0]
  have b10 : st2 P k s 10 = sum0 := by
    show run k (st1 P k s) (blkA P) 10 = sum0
    rw [a10, idxOther 10 (by decide) (by decide), ← esum0]
  have b11 : st2 P k s 11 = xh0 := by
    show run k (st1 P k s) (blkA P) 11 = xh0
    rw [a11, idxOther 11 (by decide) (by decide), ← exh0]
  have b24 : st2 P k s 24 = pb := by
    show run k (st1 P k s) (blkA P) 24 = pb
    rw [a24, idxOther 4 (by decide) (by decide),
      idxOther 3 (by decide) (by decide), en2, ← efnd0, ← ep0, ← epb]
  have hb15ne : st2 P k s 15 ≠ 0 := by rw [b15]; omega
  -- Stage 3: the trial division.
  have hndM : n % d < M := by
    have : n % d < d := Nat.mod_lt _ (by omega)
    omega
  have hdne : ¬ d = 0 := by omega
  have c25 : st3 P k s 25 = n % d := by
    show divStep 25 .urem 14 15 (st2 P k s) 25 = n % d
    simp [divStep, RegState.set, denoteOp, b14, b15, if_neg hdne,
      Nat.mod_eq_of_lt hndM]
  have cOther : ∀ j, j ≠ 25 → st3 P k s j = st2 P k s j := by
    intro j hj
    show divStep 25 .urem 14 15 (st2 P k s) j = st2 P k s j
    exact divStep_ne _ _ _ _ _ _ hj
  -- Stage 4: the trial/E block.
  have hst4 : st4 P k s = run k (run k (st3 P k s) blkB1) blkB2 := by
    show run k (st3 P k s) blkB = _
    rw [blkB_split, run_append]
  have hisTb : isT = 0 ∨ isT = 1 := by rw [eisT]; exact bit01 _
  have hfnd0b : fnd0 = 0 ∨ fnd0 = 1 := by omega
  obtain ⟨d3, d4⟩ :=
    blkB1_spec k (st3 P k s) (n % d) isT fnd0 d p0 c25
      ((cOther 16 (by decide)).trans b16) ((cOther 4 (by decide)).trans b4)
      ((cOther 15 (by decide)).trans b15) ((cOther 3 (by decide)).trans b3)
      hisTb hfnd0b hdM (by omega)
  have d3' : run k (st3 P k s) blkB1 3 = p1 := by
    rw [d3, ← ehit, ← ep1]
  have d4' : run k (st3 P k s) blkB1 4 = fnd1 := by
    rw [d4, ← ehit, ← efnd1]
  have hisEb : isE = 0 ∨ isE = 1 := by rw [eisE]; exact bitmul01 _ _
  have hpw2M : pw0 * 2 < M := by
    have h : (2 : Nat) ^ 25 < M := hMbig
    omega
  have he0M : e0 + 1 < M := by
    have := two24_lt_M
    omega
  have hpmM : pow0 * pb < M := by
    have h1 : pow0 * pb ≤ P.T * P.T := Nat.mul_le_mul hpow0T hpbT
    have h2 : P.T * P.T ≤ 2 ^ 24 * 2 ^ 24 := Nat.mul_le_mul hT2 hT2
    have h3 : (2 : Nat) ^ 24 * 2 ^ 24 < M := by decide
    omega
  obtain ⟨g5, g6, g30⟩ :=
    blkB2_spec k (run k (st3 P k s) blkB1) isE pw0 pb e0 pow0
      (by rw [blkB1_unt k _ 17 (by decide)]
          exact (cOther 17 (by decide)).trans b17)
      (by rw [blkB1_unt k _ 6 (by decide)]
          exact (cOther 6 (by decide)).trans b6)
      (by rw [blkB1_unt k _ 24 (by decide)]
          exact (cOther 24 (by decide)).trans b24)
      (by rw [blkB1_unt k _ 5 (by decide)]
          exact (cOther 5 (by decide)).trans b5)
      (by rw [blkB1_unt k _ 7 (by decide)]
          exact (cOther 7 (by decide)).trans b7)
      hisEb hpw2M he0M hpmM
  have e5' : st4 P k s 5 = e1 := by
    rw [hst4, g5, ← etw2, ← ecE, ← ee1]
  have e6' : st4 P k s 6 = pw1 := by
    rw [hst4, g6, ← etw2, ← ecE, ← epw1]
  have e30' : st4 P k s 30 = pow0 * pb := by rw [hst4, g30]
  have e3' : st4 P k s 3 = p1 := by
    rw [hst4, blkB2_unt k _ 3 (by decide), d3']
  have e4' : st4 P k s 4 = fnd1 := by
    rw [hst4, blkB2_unt k _ 4 (by decide), d4']
  have eB : ∀ j, j ≠ 25 → j ≠ 26 → j ≠ 27 → j ≠ 3 → j ≠ 4 → j ≠ 28 →
      j ≠ 29 → j ≠ 5 → j ≠ 6 → j ≠ 30 → st4 P k s j = st2 P k s j := by
    intro j h25 h26 h27 h3 h4 h28 h29 h5 h6 h30
    rw [hst4, blkB2_unt k _ j (by simp [h28, h29, h5, h6, h30]),
      blkB1_unt k _ j (by simp [h26, h27, h3, h4])]
    exact cOther j h25
  have e14 : st4 P k s 14 = n :=
    ((eB 14 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans b14)
  have he14ne : st4 P k s 14 ≠ 0 := by rw [e14]; omega
  -- Stage 5: the modular power.
  have hprn : pow0 * pb % n < n := Nat.mod_lt _ (by omega)
  have hnne : ¬ n = 0 := by omega
  have hprM0 : pr < M := by rw [epr]; omega
  have f31 : st5 P k s 31 = pr := by
    show divStep 31 .urem 30 14 (st4 P k s) 31 = pr
    simp [divStep, RegState.set, denoteOp, e30', e14, if_neg hnne, ← epr,
      Nat.mod_eq_of_lt hprM0]
  have fOther : ∀ j, j ≠ 31 → st5 P k s j = st4 P k s j := by
    intro j hj
    show divStep 31 .urem 30 14 (st4 P k s) j = st4 P k s j
    exact divStep_ne _ _ _ _ _ _ hj
  -- Stage 6: the E finish and the X numerator.
  have hpow0M : pow0 < M := by omega
  have hpw1M : pw1 < M := by
    rw [epw1]
    split <;> omega
  obtain ⟨j7, j8, j33⟩ :=
    blkC_spec k (st5 P k s) isE pr pow0 pp0 pw1 pb
      ((fOther 17 (by decide)).trans
        ((eB 17 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans b17))
      f31
      ((fOther 7 (by decide)).trans
        ((eB 7 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans b7))
      ((fOther 8 (by decide)).trans
        ((eB 8 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans b8))
      ((fOther 6 (by decide)).trans e6')
      ((fOther 24 (by decide)).trans
        ((eB 24 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans b24))
      hisEb hpb1 hpb24 hpw1M hprM0 hpow0M hpp0
  have k7 : st6 P k s 7 = pow1 := by
    show run k (st5 P k s) blkC 7 = pow1
    rw [j7, ← epow1]
  have k8 : st6 P k s 8 = pp1 := by
    show run k (st5 P k s) blkC 8 = pp1
    rw [j8, ← epp1]
  have k33 : st6 P k s 33 = SC * xn1 + (pb - 1) := by
    show run k (st5 P k s) blkC 33 = _
    rw [j33, ← exn1]
  have kOther : ∀ j, j ≠ 7 → j ≠ 8 → j ≠ 32 → j ≠ 33 →
      st6 P k s j = st5 P k s j := by
    intro j h7 h8 h32 h33
    show run k (st5 P k s) blkC j = st5 P k s j
    exact blkC_unt k _ j (by simp [h7, h8, h32, h33])
  have k24 : st6 P k s 24 = pb := by
    rw [kOther 24 (by decide) (by decide) (by decide) (by decide),
      fOther 24 (by decide)]
    exact (eB 24 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans b24
  have hk24ne : st6 P k s 24 ≠ 0 := by rw [k24]; omega
  -- Stage 7: the X division.
  have hxnM : SC * xn1 + (pb - 1) < M := by
    have h1 : xn1 ≤ pb := by
      rw [exn1]
      rcases bit01 (pw1 ≤ pb) with h | h <;> rw [h] <;> omega
    have h2 : SC * xn1 ≤ SC * 2 ^ 24 := by
      exact Nat.mul_le_mul_left _ (by omega)
    have h3 : SC * 2 ^ 24 + 2 ^ 24 < M := by decide
    omega
  have hpbne : ¬ pb = 0 := by omega
  have hxqM : xq < M := by
    rw [exq]
    have := Nat.div_le_self (SC * xn1 + (pb - 1)) pb
    omega
  have l34 : st7 P k s 34 = xq := by
    show divStep 34 .udiv 33 24 (st6 P k s) 34 = xq
    simp [divStep, RegState.set, denoteOp, k33, k24, if_neg hpbne, ← exq,
      Nat.mod_eq_of_lt hxqM]
  have lOther : ∀ j, j ≠ 34 → st7 P k s j = st6 P k s j := by
    intro j hj
    show divStep 34 .udiv 33 24 (st6 P k s) j = st6 P k s j
    exact divStep_ne _ _ _ _ _ _ hj
  -- Stage 8: the X assignment.
  have hisXb : isX = 0 ∨ isX = 1 := by rw [eisX]; exact bit01 _
  obtain ⟨m2, m11, m9, m10, m37⟩ :=
    blkD_spec k (st7 P k s) xq isX (s 2) xh0 t0 sum0
      l34
      ((lOther 18 (by decide)).trans
        ((kOther 18 (by decide) (by decide) (by decide) (by decide)).trans
          ((fOther 18 (by decide)).trans
            ((eB 18 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide)).trans b18))))
      ((lOther 2 (by decide)).trans
        ((kOther 2 (by decide) (by decide) (by decide) (by decide)).trans
          ((fOther 2 (by decide)).trans
            ((eB 2 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide)).trans b2))))
      ((lOther 11 (by decide)).trans
        ((kOther 11 (by decide) (by decide) (by decide) (by decide)).trans
          ((fOther 11 (by decide)).trans
            ((eB 11 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide)).trans b11))))
      ((lOther 9 (by decide)).trans
        ((kOther 9 (by decide) (by decide) (by decide) (by decide)).trans
          ((fOther 9 (by decide)).trans
            ((eB 9 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide)).trans b9))))
      ((lOther 10 (by decide)).trans
        ((kOther 10 (by decide) (by decide) (by decide) (by decide)).trans
          ((fOther 10 (by decide)).trans
            ((eB 10 (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide)).trans b10))))
      hisXb hs.okLe hxqM hxh027 ht0SC (by omega)
  have n2 : st8 P k s 2 = ok1 := by
    show run k (st7 P k s) blkD 2 = ok1
    rw [m2, ← egX, ← eok1]
  have n11 : st8 P k s 11 = xh1 := by
    show run k (st7 P k s) blkD 11 = xh1
    rw [m11, ← egX, ← excap, ← exh1]
  have n9 : st8 P k s 9 = t1 := by
    show run k (st7 P k s) blkD 9 = t1
    rw [m9, ← et1]
  have n10 : st8 P k s 10 = sum1 := by
    show run k (st7 P k s) blkD 10 = sum1
    rw [m10, ← esum1]
  have n37 : st8 P k s 37 = (SC - 1) + t1 * xh1 := by
    show run k (st7 P k s) blkD 37 = _
    rw [m37, ← egX, ← excap, ← exh1, ← et1]
  have nOther : ∀ j, j ≠ 35 → j ≠ 2 → j ≠ 36 → j ≠ 11 → j ≠ 9 → j ≠ 10 →
      j ≠ 37 → st8 P k s j = st7 P k s j := by
    intro j h35 h2 h36 h11 h9 h10 h37
    show run k (st7 P k s) blkD j = st7 P k s j
    exact blkD_unt k _ j (by simp [h35, h2, h36, h11, h9, h10, h37])
  -- Stage 9: the series-scale division.
  have hx1B : xh1 ≤ 2 ^ 27 := by
    rw [exh1]
    split
    · rw [excap]
      split
      · rename_i hgx
        rw [egX] at hgx
        revert hgx
        split <;> omega
      · omega
    · exact hxh027
  have ht1SC : t1 ≤ SC := by rw [et1]; split <;> omega
  have htqSC : tq ≤ SC := by rw [etq]; exact tq_le_SC ht1SC hx1B
  have htqM : tq < M := by omega
  have hSCne : ¬ SC = 0 := by decide
  have p38 : st9 P k s 38 = tq := by
    show divLitStep 38 .udiv 37 SC (st8 P k s) 38 = tq
    simp [divLitStep, RegState.set, denoteOp, n37, litSC, if_neg hSCne,
      ← etq, Nat.mod_eq_of_lt htqM]
  have pOther : ∀ j, j ≠ 38 → st9 P k s j = st8 P k s j := by
    intro j hj
    show divLitStep 38 .udiv 37 SC (st8 P k s) j = st8 P k s j
    exact divLitStep_ne _ _ _ _ _ _ hj
  -- Stage 10: the series divisor.
  have hisMb : isMv = 0 ∨ isMv = 1 := by rw [eisMv]; exact bitmul01 _ _
  obtain ⟨q39, q40⟩ :=
    blkE_spec P k (st9 P k s) isMv rr tq
      ((pOther 20 (by decide)).trans
        ((nOther 20 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans
          ((lOther 20 (by decide)).trans
            ((kOther 20 (by decide) (by decide) (by decide) (by decide)).trans
              ((fOther 20 (by decide)).trans
                ((eB 20 (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide)).trans b20))))))
      ((pOther 12 (by decide)).trans
        ((nOther 12 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans
          ((lOther 12 (by decide)).trans
            ((kOther 12 (by decide) (by decide) (by decide) (by decide)).trans
              ((fOther 12 (by decide)).trans
                ((eB 12 (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide)).trans b12))))))
      p38 hisMb
      (by intro h
          rw [eisMv] at h
          rcases bit01 (P.td + 25 ≤ rr) with h1 | h1 <;> rw [h1] at h
          · simp at h
          · rw [Nat.one_mul] at h
            revert h1
            split <;> omega)
      hrrB htd24M htqSC
  have r39 : st10 P k s 39 = dv := by
    show run k (st9 P k s) (blkE P) 39 = dv
    rw [q39, ← edv]
  have r40 : st10 P k s 40 = tq + (dv - 1) := by
    show run k (st9 P k s) (blkE P) 40 = _
    rw [q40, ← edv]
  have rOther : ∀ j, j ≠ 39 → j ≠ 40 → st10 P k s j = st9 P k s j := by
    intro j h39 h40
    show run k (st9 P k s) (blkE P) j = st9 P k s j
    exact blkE_unt P k _ j (by simp [h39, h40])
  have hdv1 : 1 ≤ dv := by
    rw [edv]
    split
    · rename_i hMv1
      have h25 : P.td + 25 ≤ rr := by
        rw [eisMv] at hMv1
        rcases bit01 (P.td + 25 ≤ rr) with h1 | h1 <;> rw [h1] at hMv1
        · simp at hMv1
        · rw [Nat.one_mul] at hMv1
          revert h1
          split <;> omega
      omega
    · omega
  have hr39ne : st10 P k s 39 ≠ 0 := by rw [r39]; omega
  -- Stage 11: the series-term division.
  have hdvne : ¬ dv = 0 := by omega
  have htermSC : term ≤ SC := by
    rw [eterm]
    exact Nat.le_trans (term_le_tq hdv1) htqSC
  have htermM : term < M := by omega
  have s41 : st11 P k s 41 = term := by
    show divStep 41 .udiv 40 39 (st10 P k s) 41 = term
    simp [divStep, RegState.set, denoteOp, r40, r39, if_neg hdvne,
      ← eterm, Nat.mod_eq_of_lt htermM]
  have sOther : ∀ j, j ≠ 41 → st11 P k s j = st10 P k s j := by
    intro j hj
    show divStep 41 .udiv 40 39 (st10 P k s) j = st10 P k s j
    exact divStep_ne _ _ _ _ _ _ hj
  -- A generic thread from `st11` back to `st2`, for registers no later stage
  -- writes.
  have thread : ∀ j, j ≠ 41 → j ≠ 39 → j ≠ 40 → j ≠ 38 → j ≠ 35 → j ≠ 2 →
      j ≠ 36 → j ≠ 11 → j ≠ 9 → j ≠ 10 → j ≠ 37 → j ≠ 34 → j ≠ 7 → j ≠ 8 →
      j ≠ 32 → j ≠ 33 → j ≠ 31 → j ≠ 25 → j ≠ 26 → j ≠ 27 → j ≠ 3 → j ≠ 4 →
      j ≠ 28 → j ≠ 29 → j ≠ 5 → j ≠ 6 → j ≠ 30 →
      st11 P k s j = st2 P k s j := by
    intro j h41 h39 h40 h38 h35 h2 h36 h11 h9 h10 h37 h34 h7 h8 h32 h33 h31
      h25 h26 h27 h3 h4 h28 h29 h5 h6 h30
    rw [sOther j h41, rOther j h39 h40, pOther j h38,
      nOther j h35 h2 h36 h11 h9 h10 h37, lOther j h34,
      kOther j h7 h8 h32 h33, fOther j h31]
    exact eB j h25 h26 h27 h3 h4 h28 h29 h5 h6 h30
  -- Bit facts for the F stages.
  have hisSb : isS = 0 ∨ isS = 1 := by rw [eisS]; exact bitmul01 _ _
  have hisLb : isL = 0 ∨ isL = 1 := by rw [eisL]; exact bit01 _
  have hisFb : isF = 0 ∨ isF = 1 := by rw [eisF]; exact bit01 _
  have hgXb : gX = 0 ∨ gX = 1 := by rw [egX]; exact bit01 _
  have hgXle : gX ≤ 1 := by rcases hgXb with h | h <;> omega
  have hisXle : isX ≤ 1 := by rcases hisXb with h | h <;> omega
  have hisEle : isE ≤ 1 := by rcases hisEb with h | h <;> omega
  have hisSle : isS ≤ 1 := by rcases hisSb with h | h <;> omega
  have hxorX : isX ^^^ 1 ≤ 1 := by
    rcases hisXb with h | h <;> subst h <;> decide
  have hxorS : isS ^^^ 1 ≤ 1 := by
    rcases hisSb with h | h <;> subst h <;> decide
  have hok1le : ok1 ≤ 1 := by
    rw [eok1]
    exact mul_le_one' hs.okLe (or_le_one hgXle hxorX)
  have hsum1C : sum1 ≤ CAP := by
    rw [esum1]
    split
    · omega
    · exact hsum0C
  -- Stage F1: guarded series accumulation.
  have hpsRunEq : psRun P k s =
      run k (run k (run k (run k (st11 P k s) blkF1) blkF2a) blkF2b)
        (blkF2c P) := by
    rw [psRun_eq_st, blkF_split, run_append, blkF2_eq, run_append, run_append]
  obtain ⟨F1_9, F1_2, F1_10⟩ :=
    blkF1_spec k (st11 P k s) isS isMv isL tq term t1 sum1 ok1
      ((thread 19 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans b19)
      ((thread 20 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans b20)
      ((thread 21 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans b21)
      ((sOther 38 (by decide)).trans ((rOther 38 (by decide)
        (by decide)).trans p38))
      s41
      ((sOther 9 (by decide)).trans ((rOther 9 (by decide)
        (by decide)).trans ((pOther 9 (by decide)).trans n9)))
      ((sOther 10 (by decide)).trans ((rOther 10 (by decide)
        (by decide)).trans ((pOther 10 (by decide)).trans n10)))
      ((sOther 2 (by decide)).trans ((rOther 2 (by decide)
        (by decide)).trans ((pOther 2 (by decide)).trans n2)))
      (by omega) (by omega) (by omega)
      htqSC htermSC hsum1C hok1le (by omega)
  have hscap' : (if sum1 + (isMv * term + isL * (2 * tq)) ≤ CAP
      then sum1 + (isMv * term + isL * (2 * tq)) else CAP) = scap := by
    rw [escap, egS, ← escn, ← esum2]
    by_cases hc : sum2 ≤ CAP <;> simp [hc]
  have F1_9' : run k (st11 P k s) blkF1 9 = t2 := by rw [F1_9, ← et2]
  have F1_2' : run k (st11 P k s) blkF1 2 = ok2 := by
    rw [F1_2, ← escn, ← esum2, ← egS, ← eok2]
  have F1_10' : run k (st11 P k s) blkF1 10 = sum3 := by
    rw [F1_10, hscap', ← esum3]
  -- Stage F2a: the λ term.
  have hpp1le : pp1 ≤ 1 := by
    have hb : (if pr = 0 then (1 : Nat) else 0) ≤ 1 := by split <;> omega
    rw [epp1]
    exact or_le_one hpp0 (mul_le_one' hisEle hb)
  have hcEle : cE ≤ 1 := by
    have hb : (if tw2 ≤ pb then (1 : Nat) else 0) ≤ 1 := by split <;> omega
    rw [ecE]
    exact mul_le_one' hisEle hb
  have he1_32 : e1 ≤ 32 := by
    rw [ee1]
    omega
  have hsum3C : sum3 ≤ CAP := by
    rw [esum3]
    split
    · rw [escap]
      split
      · rename_i hgs
        rw [egS] at hgs
        revert hgs
        split <;> omega
      · omega
    · exact hsum1C
  have F2a_46 : run k (run k (st11 P k s) blkF1) blkF2a 46 = lam := by
    rw [blkF2a_spec k _ pp1 e1 sum3
      (by rw [blkF1_unt k _ 8 (by decide)]
          exact (sOther 8 (by decide)).trans ((rOther 8 (by decide)
            (by decide)).trans ((pOther 8 (by decide)).trans
              ((nOther 8 (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide)).trans
                ((lOther 8 (by decide)).trans k8)))))
      (by rw [blkF1_unt k _ 5 (by decide)]
          exact (sOther 5 (by decide)).trans ((rOther 5 (by decide)
            (by decide)).trans ((pOther 5 (by decide)).trans
              ((nOther 5 (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide)).trans
                ((lOther 5 (by decide)).trans
                  ((kOther 5 (by decide) (by decide) (by decide)
                    (by decide)).trans ((fOther 5 (by decide)).trans e5')))))))
      F1_10' hpp1le he1_32 hsum3C, ← elam]
  -- Stage F2b: the guarded accumulator step.
  have hlamM : lam < M := by
    rw [elam]
    have hL2C : L2C < 2 ^ 28 := by decide
    have h1 : L2C * e1 ≤ L2C * 32 := Nat.mul_le_mul_left _ he1_32
    have h2 : L2C * 32 + CAP < M := by decide
    have h3 : pp1 * (L2C * e1 + sum3) ≤ L2C * e1 + sum3 := by
      rcases (show pp1 = 0 ∨ pp1 = 1 by omega) with h | h <;> simp [h]
    omega
  have hisFle : isF ≤ 1 := by omega
  have hgSle : gS ≤ 1 := by
    rw [egS]
    split <;> omega
  have hok2le : ok2 ≤ 1 := by
    rw [eok2]
    exact mul_le_one' hok1le (or_le_one hgSle hxorS)
  obtain ⟨F2b_0, F2b_2, F2b_14, F2b_1, F2b_22⟩ :=
    blkF2b_spec k (run k (run k (st11 P k s) blkF1) blkF2a) (s 0) isF lam ok2
      (by rw [blkF2a_unt k _ 0 (by decide), blkF1_unt k _ 0 (by decide)]
          exact (thread 0 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans b0)
      (by rw [blkF2a_unt k _ 22 (by decide), blkF1_unt k _ 22 (by decide)]
          exact (thread 22 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans b22)
      F2a_46
      (by rw [blkF2a_unt k _ 2 (by decide)]; exact F1_2')
      (hs.word 0) hisFle hlamM hok2le
  have F2b_0' : run k (run k (run k (st11 P k s) blkF1) blkF2a) blkF2b 0 =
      acc1 := by rw [F2b_0, ← eacc1]
  have F2b_2' : run k (run k (run k (st11 P k s) blkF1) blkF2a) blkF2b 2 =
      ok3 := by rw [F2b_2, ← eacc1, ← eok3]
  -- Stage F2c: the masked slope test.
  have hacc1M : acc1 < M := by
    rw [eacc1]
    exact Nat.mod_lt _ M_pos
  have hKM' : P.K % M = P.K := Nat.mod_eq_of_lt (by
    have h1 := hP.kSmall
    have h2 : (2 : Nat) ^ 30 < M := by decide
    omega)
  have hloM' : P.lo % M = P.lo := Nat.mod_eq_of_lt (by
    have h1 := hP.loSmall
    have h2 := hP.topSmall
    have h3 := two24_lt_M
    omega)
  obtain ⟨F2c_1, F2c_0, F2c_2⟩ :=
    blkF2c_spec P k
      (run k (run k (run k (st11 P k s) blkF1) blkF2a) blkF2b) acc1 n isF (s 1)
      F2b_0'
      (by rw [F2b_14, blkF2a_unt k _ 14 (by decide),
            blkF1_unt k _ 14 (by decide)]
          exact (thread 14 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans b14)
      F2b_22
      (by rw [F2b_1, blkF2a_unt k _ 1 (by decide),
            blkF1_unt k _ 1 (by decide)]
          exact (thread 1 (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)).trans b1)
      hacc1M hn24 hisFle hs.passLe hKM' hloM' hP.kSmall
  -- The twelve carried registers of the whole round.
  have v0 : psRun P k s 0 = acc1 := by rw [hpsRunEq]; exact F2c_0
  have v1 : psRun P k s 1 = pass1 := by
    rw [hpsRunEq, F2c_1, ← echk, ← epass1]
  have v2 : psRun P k s 2 = ok3 := by
    rw [hpsRunEq, F2c_2, F2b_2']
  have vF : ∀ j, j ≠ 48 → j ≠ 1 → j ≠ 47 → j ≠ 2 → j ≠ 0 → j ≠ 46 →
      j ≠ 9 → j ≠ 42 → j ≠ 43 → j ≠ 44 → j ≠ 45 → j ≠ 10 →
      psRun P k s j = st11 P k s j := by
    intro j h48 h1 h47 h2 h0 h46 h9 h42 h43 h44 h45 h10
    rw [hpsRunEq, blkF2c_unt P k _ j (by simp [h48, h1]),
      blkF2b_unt k _ j (by simp [h47, h2, h0]),
      blkF2a_unt k _ j (by simp [h46]),
      blkF1_unt k _ j (by simp [h9, h42, h43, h44, h2, h45, h10])]
  have v3 : psRun P k s 3 = p1 := by
    rw [vF 3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
      sOther 3 (by decide), rOther 3 (by decide) (by decide),
      pOther 3 (by decide),
      nOther 3 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      lOther 3 (by decide), kOther 3 (by decide) (by decide) (by decide)
        (by decide), fOther 3 (by decide)]
    exact e3'
  have v4 : psRun P k s 4 = fnd1 := by
    rw [vF 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
      sOther 4 (by decide), rOther 4 (by decide) (by decide),
      pOther 4 (by decide),
      nOther 4 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      lOther 4 (by decide), kOther 4 (by decide) (by decide) (by decide)
        (by decide), fOther 4 (by decide)]
    exact e4'
  have v5 : psRun P k s 5 = e1 := by
    rw [vF 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
      sOther 5 (by decide), rOther 5 (by decide) (by decide),
      pOther 5 (by decide),
      nOther 5 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      lOther 5 (by decide), kOther 5 (by decide) (by decide) (by decide)
        (by decide), fOther 5 (by decide)]
    exact e5'
  have v6 : psRun P k s 6 = pw1 := by
    rw [vF 6 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
      sOther 6 (by decide), rOther 6 (by decide) (by decide),
      pOther 6 (by decide),
      nOther 6 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      lOther 6 (by decide), kOther 6 (by decide) (by decide) (by decide)
        (by decide), fOther 6 (by decide)]
    exact e6'
  have v7 : psRun P k s 7 = pow1 := by
    rw [vF 7 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
      sOther 7 (by decide), rOther 7 (by decide) (by decide),
      pOther 7 (by decide),
      nOther 7 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      lOther 7 (by decide)]
    exact k7
  have v8 : psRun P k s 8 = pp1 := by
    rw [vF 8 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
      sOther 8 (by decide), rOther 8 (by decide) (by decide),
      pOther 8 (by decide),
      nOther 8 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide),
      lOther 8 (by decide)]
    exact k8
  have v9 : psRun P k s 9 = t2 := by
    rw [hpsRunEq, blkF2c_unt P k _ 9 (by decide),
      blkF2b_unt k _ 9 (by decide), blkF2a_unt k _ 9 (by decide)]
    exact F1_9'
  have v10 : psRun P k s 10 = sum3 := by
    rw [hpsRunEq, blkF2c_unt P k _ 10 (by decide),
      blkF2b_unt k _ 10 (by decide), blkF2a_unt k _ 10 (by decide)]
    exact F1_10'
  have v11 : psRun P k s 11 = xh1 := by
    rw [vF 11 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
      sOther 11 (by decide), rOther 11 (by decide) (by decide),
      pOther 11 (by decide)]
    exact n11
  -- Assembled: the round is `psRound`.
  have hvals : valsOf (psRun P k s) = psRound P k (valsOf s) := by
    rw [psRound_mk P k (valsOf s) rr n d isT isE isX isS isMv isL isF p0 fnd0
      e0 pw0 pow0 pp0 t0 sum0 xh0 pb hit p1 fnd1 tw2 cE e1 pw1 pr pow1 pp1
      xn1 xq gX ok1 xcap xh1 t1 sum1 tq dv term t2 scn sum2 gS ok2 scap sum3
      lam acc1 ok3 chk pass1 err en ed eisT eisE eisX eisS eisMv eisL eisF
      ep0 efnd0 ee0 epw0 epow0 epp0 et0 esum0 exh0 epb ehit ep1 efnd1 etw2
      ecE ee1 epw1 epr epow1 epp1 exn1 exq egX eok1 excap exh1 et1 esum1 etq
      edv eterm et2 escn esum2 egS eok2 escap esum3 elam eacc1 eok3 echk
      epass1]
    simp only [valsOf, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
  refine ⟨hb15ne, he14ne, hk24ne, hr39ne, hvals, ?_⟩
  -- The invariant is preserved.
  have hhitb : hit = 0 ∨ hit = 1 := by rw [ehit]; exact bit01 _
  have hisTle : isT ≤ 1 := by rcases hisTb with h | h <;> omega
  have hcEb : cE = 0 ∨ cE = 1 := by omega
  refine
    { word := psRun_lt P k s hs.word
      passLe := ?_
      okLe := ?_
      pPos := ?_
      pLe := ?_
      fndLe := ?_
      pwPow := ?_
      pwLe := ?_
      powLe := ?_
      ppLe := ?_
      tLe := ?_
      sumLe := ?_
      xhLe := ?_ }
  · rw [v1, epass1]
    have hchkle : chk ≤ 1 := by
      rw [echk]
      exact or_le_one (by split <;> omega) (by split <;> omega)
    have hxorF : isF ^^^ 1 ≤ 1 := by
      rcases hisFb with h | h <;> subst h <;> decide
    exact mul_le_one' hs.passLe (or_le_one hchkle hxorF)
  · rw [v2, eok3]
    exact mul_le_one' hok2le (by split <;> omega)
  · rw [v3, ep1]
    split
    · omega
    · exact hp0pos
  · rw [v3, ep1]
    split
    · rename_i hcond
      have hT1' : isT = 1 := by
        rcases hisTb with h | h
        · rw [h] at hcond
          simp at hcond
        · exact h
      have hrrtd : rr < P.td := by
        rw [eisT] at hT1'
        revert hT1'
        split <;> omega
      have := hdT hrrtd
      omega
    · exact hp0T
  · rw [v4, efnd1]
    refine or_le_one hfnd0 (mul_le_one' hisTle ?_)
    rcases hhitb with h | h <;> omega
  · rw [v6, v5, epw1]
    rcases hcEb with hc | hc
    · rw [if_neg (by omega), hpw0pow, ee1, hc, Nat.add_zero]
    · rw [if_pos hc, etw2, hpw0pow, ee1, hc,
        show 2 ^ e0 * 2 = 2 ^ (e0 + 1) from (Nat.pow_succ 2 e0).symm]
  · rw [v6, epw1]
    rcases hcEb with hc | hc
    · rw [if_neg (by omega)]
      exact hpw0T
    · rw [if_pos hc]
      have htwpb : tw2 ≤ pb := by
        rw [ecE] at hc
        rcases hisEb with h | h
        · rw [h] at hc
          simp at hc
        · rw [h, Nat.one_mul] at hc
          revert hc
          split <;> omega
      omega
  · rw [v7, epow1]
    split
    · rw [epr]
      have : pow0 * pb % n < n := Nat.mod_lt _ (by omega)
      omega
    · exact hpow0T
  · rw [v8]
    exact hpp1le
  · rw [v9, et2]
    split
    · exact htqSC
    · exact ht1SC
  · rw [v10]
    exact hsum3C
  · rw [v11]
    exact hx1B

end Round

/-! ## §R4 The body is defined, and agrees with `psRun` below the cursor -/

private theorem divStep_congr (dest : Nat) (op : Op) (a b : Nat)
    (ha : a < cursor) (hb : b < cursor) {u t : RegState}
    (hag : AgreeBelow cursor u t) :
    AgreeBelow cursor (divStep dest op a b u) (divStep dest op a b t) := by
  intro j hj
  by_cases hjd : j = dest
  · subst hjd
    simp [divStep, RegState.set, hag a ha, hag b hb]
  · rw [divStep_ne _ _ _ _ _ _ hjd, divStep_ne _ _ _ _ _ _ hjd]
    exact hag j hj

private theorem divLitStep_congr (dest : Nat) (op : Op) (a c : Nat)
    (ha : a < cursor) {u t : RegState} (hag : AgreeBelow cursor u t) :
    AgreeBelow cursor (divLitStep dest op a c u) (divLitStep dest op a c t) := by
  intro j hj
  by_cases hjd : j = dest
  · subst hjd
    simp [divLitStep, RegState.set, hag a ha]
  · rw [divLitStep_ne _ _ _ _ _ _ hjd, divLitStep_ne _ _ _ _ _ _ hjd]
    exact hag j hj

private theorem udivStep_denote (k dest a b : Nat) (op : Op)
    (hop : op = Op.udiv ∨ op = Op.urem) (u : RegState) (hne : u b ≠ 0) :
    denoteInstrs k u [Instr.binop dest op (.reg a) (.reg b)] =
      some (divStep dest op a b u) := by
  rcases hop with rfl | rfl <;>
    simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, divStep, hne]

private theorem udivLitStep_denote (k dest a c : Nat) (op : Op)
    (hop : op = Op.udiv ∨ op = Op.urem) (u : RegState) (hne : c % M ≠ 0) :
    denoteInstrs k u [Instr.binop dest op (.reg a) (.lit c)] =
      some (divLitStep dest op a c u) := by
  rcases hop with rfl | rfl <;>
    simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, divLitStep, hne]

private theorem idxStep_denote (R k : Nat) (u : RegState) (hne : R % M ≠ 0) :
    denoteInstrs k u
      [Instr.binop 12 .urem .idx (.lit R), Instr.binop 13 .udiv .idx (.lit R)] =
        some (idxStep R k u) := by
  simp [denoteInstrs, denoteInstr, denoteOperand, denoteOp, idxStep, hne]

private theorem blockStep_agree (k : Nat) (as : List Assign)
    (hWF : ∀ a ∈ as, a.WF cursor) (u t : RegState)
    (hag : AgreeBelow cursor u t) :
    ∃ u', denoteInstrs k u (block cursor as) = some u' ∧
      AgreeBelow cursor u' (run k t as) := by
  obtain ⟨u', h1, h2⟩ := block_correct k cursor as hWF u
  exact ⟨u', h1,
    fun r hr => (h2 r hr).trans (run_congr k cursor as hWF u t hag r hr)⟩

private theorem obindSome {α β : Type _} (a : α) (f : α → Option β) :
    (some a).bind f = f a := rfl

theorem psBody_defined (P : Params) (hP : P.Sane) (k : Nat) (s : RegState)
    (h15 : st2 P k s 15 ≠ 0) (h14 : st4 P k s 14 ≠ 0)
    (h24 : st6 P k s 24 ≠ 0) (h39 : st10 P k s 39 ≠ 0) :
    ∃ s', denoteInstrs k s (psBody P) = some s' ∧
      AgreeBelow cursor s' (psRun P k s) := by
  have hRne : P.R % M ≠ 0 := by
    rw [hP.RModM]
    have := hP.RPos
    omega
  have hSCne : SC % M ≠ 0 := by decide
  have hsplit : psBody P =
      [Instr.binop 12 .urem .idx (.lit P.R),
       Instr.binop 13 .udiv .idx (.lit P.R)] ++
      (block cursor (blkA P) ++
        ([Instr.binop 25 .urem (.reg 14) (.reg 15)] ++
          (block cursor blkB ++
            ([Instr.binop 31 .urem (.reg 30) (.reg 14)] ++
              (block cursor blkC ++
                ([Instr.binop 34 .udiv (.reg 33) (.reg 24)] ++
                  (block cursor blkD ++
                    ([Instr.binop 38 .udiv (.reg 37) (.lit SC)] ++
                      (block cursor (blkE P) ++
                        ([Instr.binop 41 .udiv (.reg 40) (.reg 39)] ++
                          block cursor (blkF P))))))))))) := by
    simp [psBody, List.append_assoc]
  obtain ⟨u2, hu2, ha2⟩ := blockStep_agree k (blkA P) (blkA_wf P)
    (idxStep P.R k s) (idxStep P.R k s)
    (AgreeBelow.refl cursor (idxStep P.R k s))
  have ha2' : AgreeBelow cursor u2 (st2 P k s) := ha2
  have hne15 : u2 15 ≠ 0 := by rw [ha2' 15 (by decide)]; exact h15
  have ha3 : AgreeBelow cursor (divStep 25 .urem 14 15 u2) (st3 P k s) :=
    divStep_congr 25 .urem 14 15 (by decide) (by decide) ha2'
  obtain ⟨u4, hu4, ha4⟩ := blockStep_agree k blkB blkB_wf
    (divStep 25 .urem 14 15 u2) (st3 P k s) ha3
  have ha4' : AgreeBelow cursor u4 (st4 P k s) := ha4
  have hne14 : u4 14 ≠ 0 := by rw [ha4' 14 (by decide)]; exact h14
  have ha5 : AgreeBelow cursor (divStep 31 .urem 30 14 u4) (st5 P k s) :=
    divStep_congr 31 .urem 30 14 (by decide) (by decide) ha4'
  obtain ⟨u6, hu6, ha6⟩ := blockStep_agree k blkC blkC_wf
    (divStep 31 .urem 30 14 u4) (st5 P k s) ha5
  have ha6' : AgreeBelow cursor u6 (st6 P k s) := ha6
  have hne24 : u6 24 ≠ 0 := by rw [ha6' 24 (by decide)]; exact h24
  have ha7 : AgreeBelow cursor (divStep 34 .udiv 33 24 u6) (st7 P k s) :=
    divStep_congr 34 .udiv 33 24 (by decide) (by decide) ha6'
  obtain ⟨u8, hu8, ha8⟩ := blockStep_agree k blkD blkD_wf
    (divStep 34 .udiv 33 24 u6) (st7 P k s) ha7
  have ha8' : AgreeBelow cursor u8 (st8 P k s) := ha8
  have ha9 : AgreeBelow cursor (divLitStep 38 .udiv 37 SC u8) (st9 P k s) :=
    divLitStep_congr 38 .udiv 37 SC (by decide) ha8'
  obtain ⟨u10, hu10, ha10⟩ := blockStep_agree k (blkE P) (blkE_wf P)
    (divLitStep 38 .udiv 37 SC u8) (st9 P k s) ha9
  have ha10' : AgreeBelow cursor u10 (st10 P k s) := ha10
  have hne39 : u10 39 ≠ 0 := by rw [ha10' 39 (by decide)]; exact h39
  have ha11 : AgreeBelow cursor (divStep 41 .udiv 40 39 u10) (st11 P k s) :=
    divStep_congr 41 .udiv 40 39 (by decide) (by decide) ha10'
  obtain ⟨u12, hu12, ha12⟩ := blockStep_agree k (blkF P) (blkF_wf P)
    (divStep 41 .udiv 40 39 u10) (st11 P k s) ha11
  refine ⟨u12, ?_, ha12⟩
  rw [hsplit, denoteInstrs_append, idxStep_denote P.R k s hRne, obindSome,
    denoteInstrs_append, hu2, obindSome,
    denoteInstrs_append,
    udivStep_denote k 25 14 15 .urem (Or.inr rfl) u2 hne15, obindSome,
    denoteInstrs_append, hu4, obindSome,
    denoteInstrs_append,
    udivStep_denote k 31 30 14 .urem (Or.inr rfl) u4 hne14, obindSome,
    denoteInstrs_append, hu6, obindSome,
    denoteInstrs_append,
    udivStep_denote k 34 33 24 .udiv (Or.inl rfl) u6 hne24, obindSome,
    denoteInstrs_append, hu8, obindSome,
    denoteInstrs_append,
    udivLitStep_denote k 38 37 SC .udiv (Or.inl rfl) u8 hSCne, obindSome,
    denoteInstrs_append, hu10, obindSome,
    denoteInstrs_append,
    udivStep_denote k 41 40 39 .udiv (Or.inl rfl) u10 hne39, obindSome,
    hu12]

/-! ## §R5 The step function the fold bridge wants -/

/-- What the emitted body actually leaves in every register. -/
def psStep (P : Params) (k : Nat) (s : RegState) : RegState :=
  (denoteInstrs k s (psBody P)).getD s

private theorem denoteInstrs_lt (k : Nat) :
    ∀ (is : List Instr) (u u' : RegState), denoteInstrs k u is = some u' →
      (∀ i, u i < M) → ∀ i, u' i < M := by
  intro is
  induction is with
  | nil =>
      intro u u' h hu i
      cases h
      exact hu i
  | cons x rest ih =>
      intro u u' h hu
      have hcons : denoteInstrs k u (x :: rest) =
          (denoteInstr k u x).bind fun s' => denoteInstrs k s' rest := rfl
      rw [hcons] at h
      cases hx : denoteInstr k u x with
      | none => rw [hx] at h; exact absurd h (by simp)
      | some u1 =>
          rw [hx, obindSome] at h
          refine ih u1 u' h ?_
          cases x with
          | mov dest src =>
              have hu1 : u1 = u.set dest (denoteOperand k u src) := by
                have : some (u.set dest (denoteOperand k u src)) = some u1 := hx
                exact (Option.some.inj this).symm
              subst hu1
              intro i
              by_cases hd : i = dest
              · subst hd
                have hlt : denoteOperand k u src < M := by
                  cases src with
                  | reg j => exact hu j
                  | lit v => exact Nat.mod_lt _ M_pos
                  | «idx» => exact Nat.mod_lt _ M_pos
                simpa [RegState.set] using hlt
              · rw [regSet_ne _ _ _ _ hd]; exact hu i
          | binop dest op l r =>
              have hb : denoteInstr k u (Instr.binop dest op l r) =
                  (denoteOp op (denoteOperand k u l)
                    (denoteOperand k u r)).bind
                      fun res => some (u.set dest res) := rfl
              rw [hb] at hx
              cases hop : denoteOp op (denoteOperand k u l)
                  (denoteOperand k u r) with
              | none => rw [hop] at hx; exact absurd hx (by simp)
              | some res =>
                  rw [hop, obindSome] at hx
                  have hu1 : u1 = u.set dest res := (Option.some.inj hx).symm
                  subst hu1
                  intro i
                  by_cases hd : i = dest
                  · subst hd
                    simpa [RegState.set] using denoteOp_lt op _ _ res hop
                  · rw [regSet_ne _ _ _ _ hd]; exact hu i

/-- The machine step, at a visited index and under the invariant: defined,
agreeing with `psRun` below the cursor, and invariant-preserving. -/
theorem psStep_spec (P : Params) (hP : P.Sane) (k : Nat)
    (hk : k < P.fuel * P.R) (s : RegState) (hs : PSInv P s) :
    denoteInstrs k s (psBody P) = some (psStep P k s) ∧
      valsOf (psStep P k s) = psRound P k (valsOf s) ∧
      PSInv P (psStep P k s) := by
  obtain ⟨h15, h14, h24, h39, hv, hI⟩ := psRun_spec hP hk hs
  obtain ⟨u, hu, hag⟩ := psBody_defined P hP k s h15 h14 h24 h39
  have hstep : psStep P k s = u := by simp [psStep, hu]
  refine ⟨by rw [hstep]; exact hu, ?_, ?_⟩
  · rw [hstep, ← hv]
    show (⟨u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, u 9, u 10, u 11⟩ :
      Vals) = _
    rw [hag 0 (by decide), hag 1 (by decide), hag 2 (by decide),
      hag 3 (by decide), hag 4 (by decide), hag 5 (by decide),
      hag 6 (by decide), hag 7 (by decide), hag 8 (by decide),
      hag 9 (by decide), hag 10 (by decide), hag 11 (by decide)]
    rfl
  · rw [hstep]
    exact
      { word := denoteInstrs_lt k (psBody P) s u hu hs.word
        passLe := by rw [hag 1 (by decide)]; exact hI.passLe
        okLe := by rw [hag 2 (by decide)]; exact hI.okLe
        pPos := by rw [hag 3 (by decide)]; exact hI.pPos
        pLe := by rw [hag 3 (by decide)]; exact hI.pLe
        fndLe := by rw [hag 4 (by decide)]; exact hI.fndLe
        pwPow := by
          rw [hag 6 (by decide), hag 5 (by decide)]; exact hI.pwPow
        pwLe := by rw [hag 6 (by decide)]; exact hI.pwLe
        powLe := by rw [hag 7 (by decide)]; exact hI.powLe
        ppLe := by rw [hag 8 (by decide)]; exact hI.ppLe
        tLe := by rw [hag 9 (by decide)]; exact hI.tLe
        sumLe := by rw [hag 10 (by decide)]; exact hI.sumLe
        xhLe := by rw [hag 11 (by decide)]; exact hI.xhLe }

/-! ## §R6 The initialisation, the epilogue, and the whole program -/

/-- The carried registers after `psInit`. -/
def psInitVals : Vals := ⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩

/-- The register file after `psInit`. -/
def psInitState : RegState :=
  ((((initialState.set 1 (1 % M)).set 2 (1 % M)).set 3 (1 % M)).set
    6 (1 % M)).set 7 (1 % M)

theorem psInit_denote :
    denoteInstrs 0 initialState psInit = some psInitState := rfl

theorem psInitState_vals :
    psInitState 0 = 0 ∧ psInitState 1 = 1 ∧ psInitState 2 = 1 ∧
    psInitState 3 = 1 ∧ psInitState 4 = 0 ∧ psInitState 5 = 0 ∧
    psInitState 6 = 1 ∧ psInitState 7 = 1 ∧ psInitState 8 = 0 ∧
    psInitState 9 = 0 ∧ psInitState 10 = 0 ∧ psInitState 11 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [psInitState, RegState.set, initialState, lit1]

theorem valsOf_psInitState : valsOf psInitState = psInitVals := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ :=
    psInitState_vals
  simp [valsOf, psInitVals, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]

theorem psInitState_inv (P : Params) (hP : P.Sane) : PSInv P psInitState := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ :=
    psInitState_vals
  have hT1 : 1 ≤ P.T := by
    have := hP.fuelPos
    have := hP.startPos
    show 1 ≤ P.start + P.fuel
    omega
  exact
    { word := by
        intro i
        simp only [psInitState, RegState.set, initialState]
        split
        · exact Nat.mod_lt _ M_pos
        · split
          · exact Nat.mod_lt _ M_pos
          · split
            · exact Nat.mod_lt _ M_pos
            · split
              · exact Nat.mod_lt _ M_pos
              · split
                · exact Nat.mod_lt _ M_pos
                · exact M_pos
      passLe := by rw [e1]; omega
      okLe := by rw [e2]; omega
      pPos := by rw [e3]; omega
      pLe := by rw [e3]; exact hT1
      fndLe := by rw [e4]; omega
      pwPow := by rw [e6, e5]
      pwLe := by rw [e6]; exact hT1
      powLe := by rw [e7]; exact hT1
      ppLe := by rw [e8]; omega
      tLe := by rw [e9]; omega
      sumLe := by rw [e10]; omega
      xhLe := by rw [e11]; omega }

/-- The epilogue's effect. -/
def psFin (u : RegState) : RegState := u.set 49 ((u 1 * u 2) % M)

theorem psEpilogue_denote (u : RegState) :
    denoteInstrs 0 u psEpilogue = some (psFin u) := rfl

theorem psFin_out (u : RegState) : psFin u 49 = (u 1 * u 2) % M := by
  simp [psFin, RegState.set]

/-- Every prefix of the loop carries the invariant, and reads off as the
corresponding prefix of the `psRound` fold. -/
theorem psFold_spec (P : Params) (hP : P.Sane) :
    ∀ N, N ≤ P.fuel * P.R → ∀ u, PSInv P u →
      valsOf ((List.range N).foldl (fun w i => psStep P i w) u) =
          (List.range N).foldl (fun v i => psRound P i v) (valsOf u) ∧
        PSInv P ((List.range N).foldl (fun w i => psStep P i w) u) := by
  intro N
  induction N with
  | zero => intro _ u hu; exact ⟨rfl, hu⟩
  | succ N ih =>
      intro hN u hu
      obtain ⟨ihv, ihI⟩ := ih (by omega) u hu
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
      obtain ⟨_, hv, hI⟩ := psStep_spec P hP N (by omega) _ ihI
      exact ⟨by rw [hv, ihv], hI⟩

/-- The final carried state of the whole scan. -/
def psFinalVals (P : Params) : Vals :=
  (List.range (P.fuel * P.R)).foldl (fun v k => psRound P k v) psInitVals

/-- **The program denotes the flat fold**: the output register holds
`pass · ok` of the `psRound` fold. -/
theorem psProgram_denote (P : Params) (hP : P.Sane) :
    (psProgram P).denote =
      some ((psFinalVals P).pass * (psFinalVals P).ok) := by
  have hI0 := psInitState_inv P hP
  have hden := RS62LadderEncoding.Program.denote_eq_foldl_mem (psProgram P)
    (PSInv P) (psStep P) psFin psInitState psInit_denote hI0
    (fun index u hidx hu => (psStep_spec P hP index hidx u hu).1)
    (fun index u hidx hu => (psStep_spec P hP index hidx u hu).2.2)
    (fun u _ => psEpilogue_denote u)
  obtain ⟨hFv, hFI⟩ :=
    psFold_spec P hP (P.fuel * P.R) (Nat.le_refl _) psInitState hI0
  rw [valsOf_psInitState] at hFv
  have hpass :
      ((List.range (P.fuel * P.R)).foldl
        (fun w i => psStep P i w) psInitState) 1 = (psFinalVals P).pass :=
    congrArg Vals.pass hFv
  have hok :
      ((List.range (P.fuel * P.R)).foldl
        (fun w i => psStep P i w) psInitState) 2 = (psFinalVals P).ok :=
    congrArg Vals.ok hFv
  have hpassLe := hFI.passLe
  have hokLe := hFI.okLe
  rw [hpass] at hpassLe
  rw [hok] at hokLe
  rw [hden]
  show some (psFin ((List.range (P.fuel * P.R)).foldl
    (fun w i => psStep P i w) psInitState) 49) = _
  rw [psFin_out, hpass, hok,
    Nat.mod_eq_of_lt (by
      have h := Nat.mul_le_mul hpassLe hokLe
      have : (1 : Nat) < M := by decide
      omega)]

end LeanCompCert.Ports.PsiFixedCheck

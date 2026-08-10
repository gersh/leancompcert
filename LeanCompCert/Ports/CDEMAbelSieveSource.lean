import LeanCompCert.Ports.CDEMAbelSieveReady

/-! # Source-shaped finite Möbius rows for the CDEM sieve -/

namespace LeanCompCert.Ports.CDEMAbelSieveSource

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSievePrefix
open LeanCompCert.Ports.CDEMAbelSieveTelescope

def toPrimeTrial (s : SieveFactorState) : Ref.PrimeTrial :=
  ⟨s.m, s.par, s.sqf⟩

theorem sieveFactorStep_source (s : SieveFactorState) (p : Nat) :
    toPrimeTrial (sieveFactorStep s p) =
      Ref.primeTrialStep (toPrimeTrial s) p := by
  rfl

def sieveFactorFold (primes : List Nat) (n : Nat) : SieveFactorState :=
  primes.foldl sieveFactorStep ⟨n, 0, 1⟩

theorem sieveFactorFold_source (primes : List Nat) (n : Nat) :
    toPrimeTrial (sieveFactorFold primes n) =
      primes.foldl Ref.primeTrialStep ⟨n, 0, 1⟩ := by
  have aux : ∀ (ps : List Nat) (s : SieveFactorState),
      toPrimeTrial (ps.foldl sieveFactorStep s) =
        ps.foldl Ref.primeTrialStep (toPrimeTrial s) := by
    intro ps
    induction ps with
    | nil => intro s; rfl
    | cons p ps ih =>
        intro s
        simp only [List.foldl_cons]
        rw [ih, sieveFactorStep_source]
  exact aux primes ⟨n, 0, 1⟩

theorem sieveFactorFold_code_source (primes : List Nat) (n : Nat) :
    let s := sieveFactorFold primes n
    sieveCodeOf s.m s.par s.sqf = Ref.muCodeWith primes n := by
  unfold Ref.muCodeWith
  rw [← sieveFactorFold_source]
  rfl

theorem sieveFactorFold_code_for (kBound n : Nat) :
    let primes := LeanCompCert.Ports.ArraySegSieve.primesBelow
      (Nat.sqrt kBound + 1)
    let s := sieveFactorFold primes n
    sieveCodeOf s.m s.par s.sqf = Ref.muCodeFor kBound n := by
  exact sieveFactorFold_code_source _ _

theorem sieveRow_zero (s : SieveState) (hpj : s.pj = 0) :
    s.row = sieveFactorStep ⟨s.n, 0, 1⟩ (s.arr 0) := by
  simp [SieveState.row, sieveResetStep, sieveResetM, sieveResetPar,
    sieveResetSqf, sieveResetKeep, sieveFirst, hpj, M]

theorem sieveRow_nonzero (s : SieveState) (hpj : s.pj ≠ 0)
    (hpar : s.par < M) (hsqf : s.sqf < M) :
    s.row = sieveFactorStep ⟨s.m, s.par, s.sqf⟩ (s.arr s.pj) := by
  have hkeep : sieveResetKeep 0 = 1 := by decide
  have hpmod : s.par % M = s.par := Nat.mod_eq_of_lt hpar
  have hsmod : s.sqf % M = s.sqf := Nat.mod_eq_of_lt hsqf
  simp [SieveState.row, sieveResetStep, sieveResetM, sieveResetPar,
    sieveResetSqf, sieveFirst, hpj, hkeep, hpmod, hsmod]

theorem sieveFactorStep_word (s : SieveFactorState) (p : Nat)
    (hm : s.m < M) :
    let out := sieveFactorStep s p
    out.m < M ∧ out.par < M ∧ out.sqf < M := by
  unfold sieveFactorStep sieveNextM sieveHit sieveKeep sieveRepeated
  dsimp only
  constructor
  · split
    · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
    · exact hm
  constructor
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)

end LeanCompCert.Ports.CDEMAbelSieveSource

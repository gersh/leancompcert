import LeanCompCert.Ports.RamareCombined100MProgramV3

/-!
# Definitional allocation equations for combined-sweep programs

These generic equations keep concrete clients from reducing large closed
configuration tables merely to discover an `AProgram.arrayLen` field.
-/

namespace LeanCompCert.Ports.RamareCombined100M

/-- Reusable base-zero placement rule for any array allocation. -/
theorem baseOk_zero_of_bytes {len : Nat}
    (hbytes : 8 * len ≤ LeanCompCert.Verified.Reflect.M) :
    LeanCompCert.Verified.ArrayState.BaseOk len 0 :=
  ⟨Int.le_refl 0, by
    simpa only [Int.zero_add] using Int.ofNat_le.mpr hbytes⟩

theorem LambdaPsiSweep.program_arrayLen
    (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed) :
    (LambdaPsiSweep.program c sd).arrayLen = c.arrayLen := by
  rfl

theorem ProgramV3.program_arrayLen
    (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat) :
    (ProgramV3.program c sd weighted lo hi gammaLo gammaHi bound limit
      cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
      egammaHi).arrayLen = c.arrayLen + 1 := by
  rfl

/-- A byte-size bound gives the standard base-zero placement for any V3
program, without exposing a concrete configuration to reduction. -/
theorem ProgramV3.program_baseOk_zero_of_bytes
    (c : LambdaPsiSweep.Cfg) (sd : LambdaPsiSweep.Seed)
    (weighted : Nat) (lo hi : Int)
    (gammaLo gammaHi bound limit cgammaLo cgammaHi cbound lower
      logLen loBase hiBase sink egammaLo egammaHi : Nat)
    (hbytes : 8 * (c.arrayLen + 1) ≤
      LeanCompCert.Verified.Reflect.M) :
    LeanCompCert.Verified.ArrayState.BaseOk
      (ProgramV3.program c sd weighted lo hi gammaLo gammaHi bound limit
        cgammaLo cgammaHi cbound lower logLen loBase hiBase sink egammaLo
        egammaHi).arrayLen 0 := by
  rw [ProgramV3.program_arrayLen]
  exact baseOk_zero_of_bytes hbytes

end LeanCompCert.Ports.RamareCombined100M

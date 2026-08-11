import LeanCompCert.Ports.RamareCombined100MLambdaPsiSweep

/-!
# Generic decomposition of the lambda/psi initializer

This lemma keeps a potentially large shape initializer opaque while exposing
the two finite seed blocks and the finite log-table store between them.
-/

namespace LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant

open LeanCompCert.Verified.ArrayState (AState initialAState)
open LeanCompCert.Verified.ArrayFoldBridge (arun arun_append)
open LeanCompCert.Ports.PsiSegSieve (storeLits seedRegs)
open LeanCompCert.Ports.RamareCombined100M

theorem lambdaPsi_init_run_eq
    (c : LambdaPsiSweep.Cfg) (seed : LambdaPsiSweep.Seed)
    (shapeInitState : AState)
    (hinit : shapeInitState = arun 0 initialAState c.shape.init) :
    arun 0 initialAState (LambdaPsiSweep.init c seed) =
      arun 0
        (arun 0
          (arun 0 shapeInitState
            (seedRegs [(LambdaPsiSweep.lRLogL, seed.log.logL),
              (LambdaPsiSweep.lRLogU, seed.log.logU)]))
          (storeLits c.logCells))
        (seedRegs [(LambdaPsiSweep.rSumL, seed.sumL),
          (LambdaPsiSweep.rSumU, seed.sumU),
          (LambdaPsiSweep.rPsiLQ, seed.psiL.q),
          (LambdaPsiSweep.rPsiLR, seed.psiL.r),
          (LambdaPsiSweep.rPsiUQ, seed.psiU.q),
          (LambdaPsiSweep.rPsiUR, seed.psiU.r)]) := by
  simp only [LambdaPsiSweep.init,
    LeanCompCert.Ports.RamareCombined100M.LogSweep.init, arun_append]
  rw [hinit]

end LeanCompCert.Ports.RamareCombined100M.WholeSweepInvariant

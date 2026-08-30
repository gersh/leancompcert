import LeanCompCert.Verified.ClightContract

namespace LeanCompCertTests.ClightContractTest

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ClightContract

def safeShift : Program := {
  regCount := 2
  loopCount := 1
  init := [.mov 0 (.lit 7)]
  body := [.binop 1 .shl (.reg 0) (.lit 3)]
  epilogue := []
  output := 1
}

def oversizedShift : Program := {
  regCount := 2
  loopCount := 1
  init := [.mov 0 (.lit 7)]
  body := [.binop 1 .shl (.reg 0) (.lit 64)]
  epilogue := []
  output := 1
}

def zeroDivisor : Program := {
  regCount := 2
  loopCount := 0
  init := [.binop 1 .udiv (.lit 7) (.lit 0)]
  body := []
  epilogue := []
  output := 1
}

example : safeShift.CompCertWF := by native_decide

/-- The static route does not unroll the computation, even at a huge bound. -/
def billionSafeShifts : Program := { safeShift with loopCount := 1000000000 }

example : billionSafeShifts.CompCertWF := by
  refine ⟨by native_decide, programSafe_of_static billionSafeShifts ?_ ?_ ?_⟩
  all_goals native_decide
example : ¬ oversizedShift.CompCertWF := by native_decide
example : ¬ zeroDivisor.CompCertWF := by native_decide

example : safeShift.denote = some 56 := by native_decide

example : safeShift.denote = some
    ((LeanCompCert.Verified.InstrBlock.srun 0
      (runIterations safeShift.body (List.range safeShift.loopCount)
        (LeanCompCert.Verified.InstrBlock.srun 0 initialState safeShift.init))
      safeShift.epilogue) safeShift.output) := by
  exact program_denote_eq_totalRun safeShift (by native_decide)

def safeArrayStore : AProgram := {
  regCount := 2
  arrayLen := 1
  loopCount := 0
  init := [
    .scalar (.mov 0 (.lit 0)),
    .scalar (.mov 1 (.lit 9)),
    .store 0 1
  ]
  body := []
  epilogue := [.load 1 0]
  output := 1
}

example : safeArrayStore.CompCertWF := by native_decide
example : safeArrayStore.denote = some 9 := by native_decide

def outOfBoundsArrayLoad : AProgram := {
  regCount := 1
  arrayLen := 0
  loopCount := 0
  init := [.load 0 0]
  body := []
  epilogue := []
  output := 0
}

example : ¬ outOfBoundsArrayLoad.CompCertWF := by native_decide

end LeanCompCertTests.ClightContractTest

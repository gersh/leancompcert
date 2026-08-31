import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceComposition

/-! Exact source decomposition used by the one-record telescope. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.DirichletLadder

def historicalBodyPrefix (c : Cfg) := c.bodyBlock.take 129
def historicalBodyFlags (c : Cfg) := (c.bodyBlock.drop 129).take 53
def historicalBodyHeightCoverage (c : Cfg) := (c.bodyBlock.drop 182).take 26
def historicalBodyTail (c : Cfg) := c.bodyBlock.drop 208

theorem adjacentSlices (l : List AInstr) (start n m : Nat) :
    (l.drop start).take n ++ (l.drop (start + n)).take m =
      (l.drop start).take (n + m) := by
  rw [List.take_add, List.drop_drop]

theorem historicalBody_eq_four_cuts (c : Cfg) : c.bodyBlock =
    historicalBodyPrefix c ++ historicalBodyFlags c ++
      historicalBodyHeightCoverage c ++ historicalBodyTail c := by
  have fourCuts (l : List AInstr) : l =
      l.take 129 ++ (l.drop 129).take 53 ++
        (l.drop 182).take 26 ++ l.drop 208 := by
    calc
      l = l.take 208 ++ l.drop 208 := (List.take_append_drop 208 l).symm
      _ = (l.take 182 ++ (l.drop 182).take 26) ++ l.drop 208 := by
        exact congrArg (fun x => x ++ l.drop 208)
          (List.take_add (l := l) (i := 182) (j := 26))
      _ = ((l.take 129 ++ (l.drop 129).take 53) ++
          (l.drop 182).take 26) ++ l.drop 208 := by
        exact congrArg (fun x => (x ++ (l.drop 182).take 26) ++ l.drop 208)
          (List.take_add (l := l) (i := 129) (j := 53))
      _ = l.take 129 ++ (l.drop 129).take 53 ++
          (l.drop 182).take 26 ++ l.drop 208 := by simp only [List.append_assoc]
  simpa only [historicalBodyPrefix, historicalBodyFlags,
    historicalBodyHeightCoverage, historicalBodyTail] using fourCuts c.bodyBlock

theorem historicalBodyPrefix_eq_cuts (c : Cfg) : historicalBodyPrefix c =
    historicalLoad c ++ historicalEarly c ++ historicalDerived c := by rfl

theorem historicalBodyFlags_eq_cuts (c : Cfg) : historicalBodyFlags c =
    historicalFlag9 c ++ historicalFlag10 c ++ historicalFlag11 c ++
    historicalFlag12 c ++ historicalFlag13 c ++ historicalFlag14 c ++
    historicalFlag15 c ++ historicalParity c ++
    [] := by rfl

theorem historicalBodyHeightCoverage_eq_cuts (c : Cfg) :
    historicalBodyHeightCoverage c =
    historicalHeightQ c ++ historicalHeightOdd c ++
    historicalHeightComplement c ++ historicalHeightEvenMul c ++
    historicalHeightCQSum c ++ historicalHeightAlt c ++
    historicalHeightSelectBit c ++ historicalHeightSelectAlt c ++
    historicalHeightSelectComplement c ++ historicalHeightSelectFloor c ++
    historicalHeightSelectSum c ++ historicalHeightFlag c ++
    historicalCoverageSucc c ++ historicalCoverageFive c ++
    historicalCoverageQ c ++ historicalCoverageCmp c ++
    historicalCoverageGate c ++ historicalCoverageBump c ++
    historicalOvershootFive c ++ historicalOvershootQ c ++
    historicalOvershootCmp c ++ historicalOvershootGate c ++
    historicalOvershootBump c := by
  simp only [historicalBodyHeightCoverage, historicalHeightQ,
    historicalHeightOdd, historicalHeightComplement,
    historicalHeightEvenMul, historicalHeightCQSum, historicalHeightAlt,
    historicalHeightSelectBit, historicalHeightSelectAlt,
    historicalHeightSelectComplement, historicalHeightSelectFloor,
    historicalHeightSelectSum, historicalHeightFlag,
    historicalCoverageSucc, historicalCoverageFive, historicalCoverageQ,
    historicalCoverageCmp, historicalCoverageGate, historicalCoverageBump,
    historicalOvershootFive, historicalOvershootQ, historicalOvershootCmp,
    historicalOvershootGate, historicalOvershootBump]
  repeat rw [adjacentSlices]

theorem historicalBodyTail_eq_cuts (c : Cfg) : historicalBodyTail c =
    historicalFlag24 c ++ historicalFlag25 c ++
    historicalFlag21 c ++ historicalFlag22 c ++ historicalFlag23 c ++
    [digestMulInstr, digestAddInstr, digestCompareInstr, digestBumpInstr] ++
    historicalStateMux c ++ historicalStateCopies c := by
  rw [← c.bodyBlock_digest]
  simp only [historicalBodyTail, historicalFlag24, historicalFlag25,
    historicalFlag21, historicalFlag22, historicalFlag23,
    historicalStateMux, historicalStateCopies]
  repeat rw [adjacentSlices]
  rfl

end LeanCompCert.Ports.DirichletLadderExternalSafety

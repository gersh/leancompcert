import LeanCompCert.Verified.Decide
import LeanCompCert.Testing.VerifiedDecide

open LeanCompCert.Verified

theorem kernelArithmetic : 1 + 1 = 2 := by
  verified_decide

theorem directKernelArithmetic : 2 + 2 = 4 := by
  decide +kernel

#print axioms kernelArithmetic
#print axioms LeanCompCert.Testing.VerifiedDecide.kernel_list_range
#print axioms LeanCompCert.Testing.VerifiedDecide.source_computation_returns_42
#print axioms LeanCompCert.Testing.VerifiedDecide.generated_c_model_returns_42

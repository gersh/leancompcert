import LeanCompCert.Ports.CDEMAbelMarkBudgetCheckDenote

namespace LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

open LeanCompCert.Verified

set_option maxHeartbeats 1000000 in
theorem program_denote_raw : program.denote =
    some (((List.range program.loopCount).foldl
      (fun a index => gstep index a) (obs entry)).acc) := by
  refine FoldBridge.Program.denote_eq_obs_foldl_mem program Inv step obs
    gstep Abs.acc entry entry_init entry_inv ?_ ?_ ?_ ?_
  · intro index s hidx hI
    exact body_denote index s hidx hI
  · intro index s hidx hI
    exact step_inv index s hidx hI
  · intro index s hidx hI
    exact body_obs index s hidx hI
  · intro s _
    rfl

end LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

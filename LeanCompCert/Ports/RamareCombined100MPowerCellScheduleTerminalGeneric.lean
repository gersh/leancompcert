import LeanCompCert.Ports.RamareCombined100MPowerCellSchedulePrefixBoundsA

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

/-- Two runs from the same initial state agree once both have reached the
terminal cursor.  The proof uses additivity of fuel and the terminal
fixed-point theorem, so it never reduces either concrete fuel value. -/
theorem powerCellRun_eq_of_terminal
    (c : Cfg) (fuel total w i : Nat) (table : Nat → Nat)
    (initial : PowerCellState)
    (hhi : 1 ≤ c.hi)
    (hfinal : (powerCellRun c fuel w i table initial).cursor =
      { pi := c.tableLen, pow := 1, base := 1, j := c.segLen + 1 })
    (hendpoint : (powerCellRun c total w i table initial).cursor =
      { pi := c.tableLen, pow := 1, base := 1, j := c.segLen + 1 }) :
    powerCellRun c fuel w i table initial =
      powerCellRun c total w i table initial := by
  let final := powerCellRun c fuel w i table initial
  let endpoint := powerCellRun c total w i table initial
  by_cases hle : fuel ≤ total
  · have hsum : fuel + (total - fuel) = total := by omega
    have hrun : endpoint = powerCellRun c (total - fuel) w i table final := by
      calc
        endpoint = powerCellRun c (fuel + (total - fuel)) w i table initial :=
          congrArg (fun n => powerCellRun c n w i table initial) hsum.symm
        _ = powerCellRun c (total - fuel) w i table
            (powerCellRun c fuel w i table initial) :=
              powerCellRun_add c fuel (total - fuel) w i table initial
        _ = powerCellRun c (total - fuel) w i table final := rfl
    have hslack := powerCellRun_terminal_slack c (total - fuel) w i table
      final hhi hfinal
    rw [hslack] at hrun
    exact hrun.symm
  · have hsum : total + (fuel - total) = fuel := by omega
    have hrun : final = powerCellRun c (fuel - total) w i table endpoint := by
      calc
        final = powerCellRun c (total + (fuel - total)) w i table initial :=
          congrArg (fun n => powerCellRun c n w i table initial) hsum.symm
        _ = powerCellRun c (fuel - total) w i table
            (powerCellRun c total w i table initial) :=
              powerCellRun_add c total (fuel - total) w i table initial
        _ = powerCellRun c (fuel - total) w i table endpoint := rfl
    have hslack := powerCellRun_terminal_slack c (fuel - total) w i table
      endpoint hhi hendpoint
    rw [hslack] at hrun
    exact hrun

/-- A symbolic prefix of a bounded, terminal run satisfies the local marking
precondition whenever its cursor is live.  Keeping the endpoint and fuel
abstract prevents large certified production tables from being reduced while
this structural argument is elaborated. -/
theorem powerCellRun_markPre_of_endpoint_bounds
    (c : Cfg) (fuel total w i : Nat) (table : Nat → Nat)
    (initial : PowerCellState)
    (hhi : 0 < c.hi)
    (hinitial : PowerCursorBounds c.segLen c.hi c.tableLen table initial.cursor)
    (hinitialBase : initial.cursor.base ≤ 10000)
    (htableBase : ∀ pi, pi ≤ c.tableLen → table pi ≤ 10000)
    (hendpointBounds :
      PlaneCellProductionBounds (powerCellRun c total w i table initial).cell)
    (hendpointTerminal : (powerCellRun c total w i table initial).cursor =
      { pi := c.tableLen, pow := 1, base := 1, j := c.segLen + 1 })
    (hlive : (powerCellRun c fuel w i table initial).cursor.j < c.segLen) :
    let pure := powerCellRun c fuel w i table initial
    PlaneCellMarkPre pure.cursor.pow pure.cursor.base pure.cell := by
  dsimp only
  let pure := powerCellRun c fuel w i table initial
  have hpure : PowerCursorBounds c.segLen c.hi c.tableLen table pure.cursor :=
    powerCellRun_cursor_bounds c fuel w i table initial hinitial hhi
  have hbaseMax : pure.cursor.base ≤ 10000 :=
    powerCellRun_base_le c fuel w i 10000 table initial hinitialBase htableBase
  by_cases hbefore : fuel ≤ total
  · have hsum : fuel + (total - fuel) = total := by omega
    have hcell := PlaneCellProductionBounds.powerCellRun_prefix
      c fuel (total - fuel) w i table initial hinitial hhi (by
        rw [hsum]
        exact hendpointBounds)
    exact PlaneCellMarkPre.of_productionBounds hcell
      (Nat.ne_of_gt hpure.base_pos) hbaseMax
  · have hsplit : fuel = total + (fuel - total) := by omega
    let endpoint := powerCellRun c total w i table initial
    have hslack := powerCellRun_terminal_slack c (fuel - total) w i table
      endpoint (Nat.succ_le_iff.mpr hhi) hendpointTerminal
    have hpureTerminal : pure.cursor =
        { pi := c.tableLen, pow := 1, base := 1, j := c.segLen + 1 } := by
      change (powerCellRun c fuel w i table initial).cursor = _
      rw [hsplit, powerCellRun_add, hslack]
      exact hendpointTerminal
    have hjterminal := congrArg PowerCursor.j hpureTerminal
    change pure.cursor.j = c.segLen + 1 at hjterminal
    have hnot : ¬pure.cursor.j < c.segLen := by
      rw [hjterminal]
      omega
    exact (hnot hlive).elim

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

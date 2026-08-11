import LeanCompCert.Ports.RamareCombined100MProductionPhaseData

/-!
# Shardable phase-chain recognizer

The original recognizer recursively retained all 2,633 production phases in
one kernel reduction.  Here each adjacent transition is a separate Boolean;
closed slices of that Boolean list can be checked in independent modules and
then reassembled without reevaluating their contents.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

def powerPhaseEdgeCheck (hi limit : Nat) (table : Nat → Nat)
    (phase next : PowerPhase) : Bool :=
  decide (0 < phase.pow) &&
  if phase.pow * phase.base ≤ hi then
    decide (phase.pi ≠ limit) &&
    decide (next = ⟨phase.pi, phase.pow * phase.base, phase.base⟩)
  else
    decide (phase.pi + 1 < limit) &&
    decide (next = ⟨phase.pi + 1, table (phase.pi + 1),
      table (phase.pi + 1)⟩)

def powerPhaseTerminalCheck (hi limit : Nat) : Option PowerPhase → Bool
  | none => false
  | some phase =>
      decide (0 < phase.pow) &&
      decide (¬phase.pow * phase.base ≤ hi) &&
      decide (phase.pi + 1 = limit)

def powerPhaseEdgeChecks (hi limit : Nat) (table : Nat → Nat) :
    List PowerPhase → List Bool
  | [] => []
  | [_] => []
  | phase :: next :: rest =>
      powerPhaseEdgeCheck hi limit table phase next ::
        powerPhaseEdgeChecks hi limit table (next :: rest)

theorem PowerPhaseChain.of_edge_checks (hi limit : Nat) (table : Nat → Nat) :
    ∀ phases,
      (powerPhaseEdgeChecks hi limit table phases).all id = true →
      powerPhaseTerminalCheck hi limit phases.getLast? = true →
      PowerPhaseChain hi limit table phases := by
  intro phases
  induction phases with
  | nil => simp [powerPhaseTerminalCheck]
  | cons phase phases ih =>
      cases phases with
      | nil =>
          intro _ hterminal
          simp only [List.getLast?_singleton, powerPhaseTerminalCheck,
            Bool.and_eq_true, decide_eq_true_eq] at hterminal
          rcases hterminal with ⟨⟨hpow, hnextPow⟩, hnext⟩
          exact .terminal phase.pi phase.pow phase.base hpow hnextPow hnext
      | cons next rest =>
          intro hall hterminal
          simp only [powerPhaseEdgeChecks, List.all_cons, Bool.and_eq_true,
            id_eq] at hall
          rcases hall with ⟨hedge, htailChecks⟩
          have htailTerminal :
              powerPhaseTerminalCheck hi limit (next :: rest).getLast? = true := by
            simpa using hterminal
          have htail := ih htailChecks htailTerminal
          by_cases hfit : phase.pow * phase.base ≤ hi
          · simp only [powerPhaseEdgeCheck, Bool.and_eq_true,
              decide_eq_true_eq, hfit, if_true] at hedge
            rcases hedge with ⟨hpow, hnonterminal, heq⟩
            subst next
            exact .bump phase.pi phase.pow phase.base rest hpow hfit
              hnonterminal htail
          · simp only [powerPhaseEdgeCheck, Bool.and_eq_true,
              decide_eq_true_eq, hfit, if_false] at hedge
            rcases hedge with ⟨hpow, hnext, heq⟩
            subst next
            exact .nextBase phase.pi phase.pow phase.base rest hpow hfit
              hnext htail

def productionPowerPhaseEdgeChecks : List Bool :=
  powerPhaseEdgeChecks 100000000 productionPrimeTable.length
    certifiedProductionPowerTable certifiedProductionPowerPhases

def productionPowerPhaseShardOK (start len : Nat) : Bool :=
  ((productionPowerPhaseEdgeChecks.drop start).take len).all id

/-- Compose one checked slice with the already-composed suffix.  This theorem
only rewrites list structure; it never evaluates a production transition. -/
theorem productionPowerPhaseShardOK.prepend (start len : Nat)
    (hchunk : productionPowerPhaseShardOK start len = true)
    (hsuffix : (productionPowerPhaseEdgeChecks.drop (start + len)).all id = true) :
    (productionPowerPhaseEdgeChecks.drop start).all id = true := by
  unfold productionPowerPhaseShardOK at hchunk
  have hsplit : productionPowerPhaseEdgeChecks.drop start =
      (productionPowerPhaseEdgeChecks.drop start).take len ++
        productionPowerPhaseEdgeChecks.drop (start + len) := by
    calc
      productionPowerPhaseEdgeChecks.drop start =
          (productionPowerPhaseEdgeChecks.drop start).take len ++
            (productionPowerPhaseEdgeChecks.drop start).drop len :=
        (List.take_append_drop len
          (productionPowerPhaseEdgeChecks.drop start)).symm
      _ = (productionPowerPhaseEdgeChecks.drop start).take len ++
          productionPowerPhaseEdgeChecks.drop (start + len) := by
        rw [List.drop_drop, Nat.add_comm]
  rw [hsplit]
  rw [List.all_append, hchunk, hsuffix]
  rfl

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

import LeanCompCert.Ports.R2SegMarkingInit

/-! # Partial-denotation bridge for the finite `R₂*` marking prefix -/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

/-- A successful full program run makes every initial loop prefix successful,
and that partial prefix is exactly its total `arun` fold.  It lives beside the
R₂ port to avoid invalidating every consumer of the shared fold bridge. -/
theorem program_prefix_eq_foldl_arun_of_denote_eq_some
    (p : AProgram) (steps : Nat) {n : Nat}
    (hsteps : steps ≤ p.loopCount) (h : p.denote = some n) :
    let entry := arun 0 initialAState p.init
    (List.range steps).foldlM
        (fun s index => denoteAInstrs p.arrayLen index s p.body) entry =
      some ((List.range steps).foldl
        (fun s index => arun index s p.body) entry) := by
  unfold AProgram.denote at h
  cases hinit : denoteAInstrs p.arrayLen 0 initialAState p.init with
  | none => simp [hinit] at h
  | some entry =>
      have hentry : entry = arun 0 initialAState p.init :=
        eq_arun_of_denoteAInstrs_eq_some p.arrayLen 0 p.init
          initialAState entry hinit
      rw [hinit] at h
      change ((List.range p.loopCount).foldlM
          (fun s index => denoteAInstrs p.arrayLen index s p.body) entry).bind
          (fun s => (denoteAInstrs p.arrayLen 0 s p.epilogue).bind
            (fun s => some (s.regs p.output))) = some n at h
      cases hloop : (List.range p.loopCount).foldlM
          (fun s index => denoteAInstrs p.arrayLen index s p.body) entry with
      | none => simp [hloop] at h
      | some loopOut =>
          obtain ⟨rest, hcount⟩ := Nat.exists_eq_add_of_le hsteps
          rw [hcount, List.range_add, List.foldlM_append] at hloop
          cases hpre : (List.range steps).foldlM
              (fun s index => denoteAInstrs p.arrayLen index s p.body) entry with
          | none => simp [hpre] at hloop
          | some mid =>
              have hmid : mid = (List.range steps).foldl
                  (fun s index => arun index s p.body) entry :=
                eq_foldl_arun_of_foldlM_denote_eq_some p.arrayLen p.body
                  (List.range steps) entry mid hpre
              dsimp only
              rw [← hentry, hpre, hmid]

/-- If the full production program denotes successfully, its complete initial
marking prefix also denotes successfully.  The resulting partial state has
advanced through exactly `markSteps` rounds and has retained its window base.

The two entry equalities are kept explicit here so the inexpensive finite
schedule theorem stays independent of the separately staged initializer
proof. -/
theorem r2Program_denote_mark_prefix_position (c : R2Cfg) (seed : R2Seed)
    (n : Nat) (hden : (r2Program c seed).denote = some n)
    (hcount : 0 < c.segCount) (hL : 0 < c.segLen)
    (hperiod : c.period < M) (hloM : c.lo < M) :
    let entry := arun 0 initialAState (c.init seed)
    let out := (List.range c.markSteps).foldl
      (fun st k => arun k st c.body) entry
    (List.range c.markSteps).foldlM
        (fun st k => denoteAInstrs c.arrayLen k st c.body) entry = some out ∧
      out.regs rR = c.markSteps ∧ out.regs rW = c.lo := by
  dsimp only
  let entry := arun 0 initialAState (c.init seed)
  let out := (List.range c.markSteps).foldl
    (fun st k => arun k st c.body) entry
  have hprefix : c.markSteps ≤ c.period * c.segCount :=
    Nat.le_trans (by simp only [R2Cfg.period]; omega)
      (Nat.le_mul_of_pos_right c.period hcount)
  have hpartial := program_prefix_eq_foldl_arun_of_denote_eq_some
    (r2Program c seed) c.markSteps hprefix hden
  change (List.range c.markSteps).foldlM
      (fun st k => denoteAInstrs c.arrayLen k st c.body) entry = some out at hpartial
  have hinit := init_mark_position_run c seed hloM
  dsimp only at hinit
  have hpos := range_body_mark_position c c.markSteps entry 0 c.lo
    hinit.1 hinit.2 (by omega) hL hperiod hloM
  have hpos' : out.regs rR = c.markSteps ∧ out.regs rW = c.lo := by
    simpa only [Nat.zero_add] using hpos
  exact ⟨hpartial, hpos'⟩

#print axioms r2Program_denote_mark_prefix_position

end LeanCompCert.Ports.R2SegSieve

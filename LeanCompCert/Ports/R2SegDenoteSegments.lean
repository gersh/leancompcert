import LeanCompCert.Ports.R2SegMarkingDenotePrefix

/-!
# Partial-denotation segments for the finite `R₂*` campaign

A successful `AProgram.denote` run certifies more than its final output: every
finite slice of the loop must also have succeeded.  This leaf exposes that
fact at arbitrary offsets and at exact production-window boundaries, without
reducing the concrete 2.1e10-range trace.  It also exposes the literal
epilogue and observed output.  These are the small cached interfaces needed
by the later array/cursor telescope.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

private theorem mbind_some {α β : Type _} (a : α)
    (f : α → Option β) : ((some a : Option α) >>= f) = f a := rfl

/-- Every arbitrary finite loop segment of a successful program denotation
is successful and agrees exactly with total `arun` execution. -/
theorem program_segment_eq_foldl_arun_of_denote_eq_some
    (p : AProgram) (offset steps : Nat) {n : Nat}
    (hspan : offset + steps ≤ p.loopCount) (h : p.denote = some n) :
    let entry := arun 0 initialAState p.init
    let before := (List.range offset).foldl
      (fun s index => arun index s p.body) entry
    let indices := (List.range steps).map (fun j => offset + j)
    indices.foldlM
        (fun s index => denoteAInstrs p.arrayLen index s p.body) before =
      some (indices.foldl (fun s index => arun index s p.body) before) := by
  dsimp only
  have hoffset : offset ≤ p.loopCount := by omega
  have hpre := program_prefix_eq_foldl_arun_of_denote_eq_some
    p offset hoffset h
  have hall := program_prefix_eq_foldl_arun_of_denote_eq_some
    p (offset + steps) hspan h
  dsimp only at hpre hall
  rw [List.range_add, List.foldlM_append, hpre] at hall
  rw [mbind_some] at hall
  simpa only [List.foldl_append] using hall

/-- A successful production run certifies the exact partial semantics of
each complete `R₂*` window, starting from the preceding total-state carry. -/
theorem r2Program_denote_window_segment
    (c : R2Cfg) (seed : R2Seed) (q n : Nat)
    (hden : (r2Program c seed).denote = some n) (hq : q < c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let offset := q * c.period
    let before := (List.range offset).foldl
      (fun s index => arun index s c.body) entry
    let indices := (List.range c.period).map (fun j => offset + j)
    indices.foldlM
        (fun s index => denoteAInstrs c.arrayLen index s c.body) before =
      some (indices.foldl (fun s index => arun index s c.body) before) := by
  dsimp only
  apply program_segment_eq_foldl_arun_of_denote_eq_some
    (r2Program c seed) (q * c.period) c.period (n := n)
  · simp only [r2Program]
    rw [← Nat.succ_mul, Nat.mul_comm c.period c.segCount]
    exact Nat.mul_le_mul_right c.period (Nat.succ_le_iff.mpr hq)
  · exact hden

/-- The literal epilogue of a successful program run is itself defined,
equals total `arun`, and its observed output register is the returned value. -/
theorem program_epilogue_eq_arun_of_denote_eq_some
    (p : AProgram) (n : Nat) (h : p.denote = some n) :
    let entry := arun 0 initialAState p.init
    let loopOut := (List.range p.loopCount).foldl
      (fun s index => arun index s p.body) entry
    denoteAInstrs p.arrayLen 0 loopOut p.epilogue =
        some (arun 0 loopOut p.epilogue) ∧
      (arun 0 loopOut p.epilogue).regs p.output = n := by
  dsimp only
  unfold AProgram.denote at h
  cases hinit : denoteAInstrs p.arrayLen 0 initialAState p.init with
  | none => simp [hinit] at h
  | some entry =>
      have hentry : entry = arun 0 initialAState p.init :=
        eq_arun_of_denoteAInstrs_eq_some p.arrayLen 0 p.init
          initialAState entry hinit
      rw [hinit] at h
      rw [mbind_some] at h
      cases hloop : (List.range p.loopCount).foldlM
          (fun s index => denoteAInstrs p.arrayLen index s p.body) entry with
      | none => simp [hloop] at h
      | some loopOut =>
          have hloopOut : loopOut = (List.range p.loopCount).foldl
              (fun s index => arun index s p.body) entry :=
            eq_foldl_arun_of_foldlM_denote_eq_some p.arrayLen p.body
              (List.range p.loopCount) entry loopOut hloop
          rw [hloop] at h
          rw [mbind_some] at h
          cases hepi : denoteAInstrs p.arrayLen 0 loopOut p.epilogue with
          | none => simp [hepi] at h
          | some out =>
              have hout : out = arun 0 loopOut p.epilogue :=
                eq_arun_of_denoteAInstrs_eq_some p.arrayLen 0 p.epilogue
                  loopOut out hepi
              rw [hepi] at h
              rw [mbind_some] at h
              have houtreg : out.regs p.output = n := Option.some.inj h
              rw [← hentry, ← hloopOut]
              rw [← hout]
              exact ⟨hepi, houtreg⟩

/-- Specialization of the epilogue boundary to the literal `R₂*` program. -/
theorem r2Program_denote_epilogue
    (c : R2Cfg) (seed : R2Seed) (n : Nat)
    (hden : (r2Program c seed).denote = some n) :
    let entry := arun 0 initialAState (c.init seed)
    let loopOut := (List.range (c.period * c.segCount)).foldl
      (fun s index => arun index s c.body) entry
    denoteAInstrs c.arrayLen 0 loopOut c.epilogue =
        some (arun 0 loopOut c.epilogue) ∧
      (arun 0 loopOut c.epilogue).regs outputReg = n := by
  simpa only [r2Program] using
    program_epilogue_eq_arun_of_denote_eq_some
      (r2Program c seed) n hden

#print axioms program_segment_eq_foldl_arun_of_denote_eq_some
#print axioms r2Program_denote_window_segment
#print axioms program_epilogue_eq_arun_of_denote_eq_some
#print axioms r2Program_denote_epilogue

end LeanCompCert.Ports.R2SegSieve

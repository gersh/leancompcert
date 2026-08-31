import LeanCompCert.Ports.RamareCombined100MShapeHostMarkAddress30

/-!
# Split marking-address guard

This module joins seven separately elaborated scalar address facts.  Keeping
the address calculations opaque here avoids elaborating one large proof term
that unfolds all seven emitted address paths at once.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxHeartbeats 1000000 in
theorem markAddresses_lt_of_markRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hround : s.regs rR < c.markSteps) (hsteps : c.markSteps < M)
    (hlen : 13 * c.segLen < len)
    (hlive : ∀ j, j < c.segLen → j < M ∧
      j + c.segLen < M ∧ j + 2 * c.segLen < M ∧
      j + 3 * c.segLen < M ∧ j + 4 * c.segLen < M ∧
      j + 5 * c.segLen < M ∧ j + 6 * c.segLen < M)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let phased := arun k s (lift c.markPhaseBody)
    let reset := arun k phased c.markResetBody
    let addressed := arun k reset c.markAddressBody
    addressed.regs 30 < len ∧ addressed.regs 31 < len ∧
      addressed.regs 32 < len ∧ addressed.regs 33 < len ∧
      addressed.regs 34 < len ∧ addressed.regs 35 < len ∧
      addressed.regs 36 < len := by
  exact ⟨markAddress30_lt_of_markRound c len k s hround hsteps hlen
      hlive h7 h8 h9 h10 h11 h12 h13,
    markAddress31_lt_of_markRound c len k s hround hsteps hlen
      hlive h7 h8 h9 h10 h11 h12 h13,
    markAddress32_lt_of_markRound c len k s hround hsteps hlen
      hlive h7 h8 h9 h10 h11 h12 h13,
    markAddress33_lt_of_markRound c len k s hround hsteps hlen
      hlive h7 h8 h9 h10 h11 h12 h13,
    markAddress34_lt_of_markRound c len k s hround hsteps hlen
      hlive h7 h8 h9 h10 h11 h12 h13,
    markAddress35_lt_of_markRound c len k s hround hsteps hlen
      hlive h7 h8 h9 h10 h11 h12 h13,
    markAddress36_lt_of_markRound c len k s hround hsteps hlen
      hlive h7 h8 h9 h10 h11 h12 h13⟩

theorem markAddresses_lt_of_classRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hround : c.markSteps ≤ s.regs rR) (hsteps : c.markSteps < M)
    (hlen : 13 * c.segLen < len)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let phased := arun k s (lift c.markPhaseBody)
    let reset := arun k phased c.markResetBody
    let addressed := arun k reset c.markAddressBody
    addressed.regs 30 < len ∧ addressed.regs 31 < len ∧
      addressed.regs 32 < len ∧ addressed.regs 33 < len ∧
      addressed.regs 34 < len ∧ addressed.regs 35 < len ∧
      addressed.regs 36 < len := by
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  have hp := c.markPhaseBody_run k s hsteps
  dsimp only at hp
  have hp10 : phased.regs 10 = 0 := by
    rw [hp.1, if_neg (Nat.not_lt_of_ge hround)]
  have hr10 : reset.regs 10 = 0 :=
    (arun_frame k 10 c.markResetBody (by rfl) phased).trans hp10
  have ha := c.markAddressBody_inactive_run k reset hr10
    h7 h8 h9 h10 h11 h12 h13
  dsimp only at ha ⊢
  rcases ha with ⟨h30, h31, h32, h33, h34, h35, h36, _⟩
  exact ⟨by rw [h30]; omega, by rw [h31]; omega,
    by rw [h32]; omega, by rw [h33]; omega,
    by rw [h34]; omega, by rw [h35]; omega,
    by rw [h36]; omega⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

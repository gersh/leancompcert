import LeanCompCert.Ports.RamareCombined100MShapeHostTotality

/-!
# Split classifier-address guards

The mark- and classification-phase address cuts are kept as two independent
lemmas.  Both consume the already-proved store-free address-prefix semantics;
neither unfolds the classifier decoder or a sweep.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem classAddresses_lt_of_markRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hround : s.regs rR < c.markSteps) (hsteps : c.markSteps < M)
    (hlen : 13 * c.segLen < len)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let marked := arun k s c.markBody
    let addressed := arun k marked c.classAddressBody
    addressed.regs 131 < len ∧ addressed.regs 133 < len ∧
      addressed.regs 134 < len ∧ addressed.regs 135 < len ∧
      addressed.regs 136 < len ∧ addressed.regs 137 < len ∧
      addressed.regs 138 < len := by
  let marked := arun k s c.markBody
  have hp := c.markBody_phase_run k s hsteps
  dsimp only at hp
  have hm10 : marked.regs 10 = 1 := by rw [hp.1, if_pos hround]
  have hnclass : ¬ c.markSteps ≤ s.regs rR := by omega
  have hm11 : marked.regs 11 = 0 := by
    rw [hp.2, if_neg hnclass]
  have ha := c.classAddressBody_mark_run k marked hm10 hm11
    h7 h8 h9 h10 h11 h12 h13
  dsimp only at ha ⊢
  rcases ha with ⟨h131, h133, h134, h135, h136, h137, h138, _⟩
  exact ⟨by rw [h131]; omega, by rw [h133]; omega,
    by rw [h134]; omega, by rw [h135]; omega,
    by rw [h136]; omega, by rw [h137]; omega,
    by rw [h138]; omega⟩

theorem classAddresses_lt_of_classRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hround : c.markSteps ≤ s.regs rR) (hsteps : c.markSteps < M)
    (hR : s.regs rR < M)
    (hsum : s.regs rR - c.markSteps + s.regs rW < M)
    (h1 : s.regs rR - c.markSteps + c.segLen < M)
    (h2 : s.regs rR - c.markSteps + 2 * c.segLen < M)
    (h3 : s.regs rR - c.markSteps + 3 * c.segLen < M)
    (h4 : s.regs rR - c.markSteps + 4 * c.segLen < M)
    (h5 : s.regs rR - c.markSteps + 5 * c.segLen < M)
    (h6 : s.regs rR - c.markSteps + 6 * c.segLen < M)
    (hlen0 : s.regs rR - c.markSteps < len)
    (hlen1 : s.regs rR - c.markSteps + c.segLen < len)
    (hlen2 : s.regs rR - c.markSteps + 2 * c.segLen < len)
    (hlen3 : s.regs rR - c.markSteps + 3 * c.segLen < len)
    (hlen4 : s.regs rR - c.markSteps + 4 * c.segLen < len)
    (hlen5 : s.regs rR - c.markSteps + 5 * c.segLen < len)
    (hlen6 : s.regs rR - c.markSteps + 6 * c.segLen < len) :
    let marked := arun k s c.markBody
    let addressed := arun k marked c.classAddressBody
    addressed.regs 131 < len ∧ addressed.regs 133 < len ∧
      addressed.regs 134 < len ∧ addressed.regs 135 < len ∧
      addressed.regs 136 < len ∧ addressed.regs 137 < len ∧
      addressed.regs 138 < len := by
  let marked := arun k s c.markBody
  have hp := c.markBody_phase_run k s hsteps
  dsimp only at hp
  have hm10 : marked.regs 10 = 0 := by
    rw [hp.1, if_neg (Nat.not_lt_of_ge hround)]
  have hm11 : marked.regs 11 = 1 := by rw [hp.2, if_pos hround]
  have hmR : marked.regs rR = s.regs rR :=
    arun_frame k rR c.markBody (by rfl) s
  have hmW : marked.regs rW = s.regs rW :=
    arun_frame k rW c.markBody (by rfl) s
  have ha := c.classAddressBody_class_run k marked hm10 hm11
    (by rw [hmR]; exact hround) (by rw [hmR]; exact hR)
    (by rw [hmR, hmW]; exact hsum)
    (by rw [hmR]; exact h1) (by rw [hmR]; exact h2)
    (by rw [hmR]; exact h3) (by rw [hmR]; exact h4)
    (by rw [hmR]; exact h5) (by rw [hmR]; exact h6)
  dsimp only at ha ⊢
  rcases ha with ⟨h131, h133, h134, h135, h136, h137, h138, _⟩
  exact ⟨by rw [h131, hmR]; exact hlen0,
    by rw [h133, hmR]; exact hlen1,
    by rw [h134, hmR]; exact hlen2,
    by rw [h135, hmR]; exact hlen3,
    by rw [h136, hmR]; exact hlen4,
    by rw [h137, hmR]; exact hlen5,
    by rw [h138, hmR]; exact hlen6⟩

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

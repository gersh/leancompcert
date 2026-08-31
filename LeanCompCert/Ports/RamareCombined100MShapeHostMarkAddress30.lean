import LeanCompCert.Ports.RamareCombined100MShapeHostTotality

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem markAddress30_lt_of_markRound
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
    (arun k reset c.markAddressBody).regs 30 < len := by
  let phased := arun k s (lift c.markPhaseBody)
  let reset := arun k phased c.markResetBody
  have hp := c.markPhaseBody_run k s hsteps
  dsimp only at hp
  have hp10 : phased.regs 10 = 1 := by rw [hp.1, if_pos hround]
  have hr10 : reset.regs 10 = 1 :=
    (arun_frame k 10 c.markResetBody (by rfl) phased).trans hp10
  dsimp only
  by_cases hj : reset.regs rJ < c.segLen
  · rcases hlive _ hj with ⟨hj0, hj1, hj2, hj3, hj4, hj5, hj6⟩
    have ha := c.markAddressBody_live_run k reset hr10 hj
      hj0 hj1 hj2 hj3 hj4 hj5 hj6
    rw [ha.2.2.1]
    omega
  · have ha := c.markAddressBody_exhausted_run k reset hr10 hj
      h7 h8 h9 h10 h11 h12 h13
    rw [ha.2.2.1]
    omega

/-- The remaining six address cuts are stated independently so their proof
terms never contain the seven-way conjunction. -/
theorem markAddress31_lt_of_markRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hround : s.regs rR < c.markSteps) (hsteps : c.markSteps < M)
    (hlen : 13 * c.segLen < len)
    (hlive : ∀ j, j < c.segLen → j < M ∧ j + c.segLen < M ∧
      j + 2*c.segLen < M ∧ j + 3*c.segLen < M ∧ j + 4*c.segLen < M ∧
      j + 5*c.segLen < M ∧ j + 6*c.segLen < M)
    (h7 : 7*c.segLen<M) (h8 : 8*c.segLen<M) (h9 : 9*c.segLen<M)
    (h10 : 10*c.segLen<M) (h11 : 11*c.segLen<M)
    (h12 : 12*c.segLen<M) (h13 : 13*c.segLen<M) :
    let p := arun k s (lift c.markPhaseBody)
    let z := arun k p c.markResetBody
    (arun k z c.markAddressBody).regs 31 < len := by
  let p := arun k s (lift c.markPhaseBody)
  let z := arun k p c.markResetBody
  have hp := c.markPhaseBody_run k s hsteps; dsimp only at hp
  have hp10 : p.regs 10 = 1 := by rw [hp.1, if_pos hround]
  have hz10 : z.regs 10 = 1 := (arun_frame k 10 c.markResetBody (by rfl) p).trans hp10
  dsimp only; by_cases hj : z.regs rJ < c.segLen
  · rcases hlive _ hj with ⟨a,b,d,e,f,g,h⟩
    rw [(c.markAddressBody_live_run k z hz10 hj a b d e f g h).2.2.2.1]; omega
  · rw [(c.markAddressBody_exhausted_run k z hz10 hj h7 h8 h9 h10 h11 h12 h13).2.2.2.1]; omega

theorem markAddress32_lt_of_markRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState) (hround : s.regs rR < c.markSteps)
    (hsteps : c.markSteps < M) (hlen : 13*c.segLen<len)
    (hlive : ∀ j, j<c.segLen → j<M ∧ j+c.segLen<M ∧ j+2*c.segLen<M ∧
      j+3*c.segLen<M ∧ j+4*c.segLen<M ∧ j+5*c.segLen<M ∧ j+6*c.segLen<M)
    (h7 : 7*c.segLen<M) (h8 : 8*c.segLen<M) (h9 : 9*c.segLen<M)
    (h10 : 10*c.segLen<M) (h11 : 11*c.segLen<M) (h12 : 12*c.segLen<M)
    (h13 : 13*c.segLen<M) :
    let p:=arun k s (lift c.markPhaseBody)
    let z:=arun k p c.markResetBody
    (arun k z c.markAddressBody).regs 32<len := by
  let p:=arun k s (lift c.markPhaseBody)
  let z:=arun k p c.markResetBody
  have hp:=c.markPhaseBody_run k s hsteps; dsimp only at hp
  have hp10:p.regs 10=1:=by rw [hp.1,if_pos hround]
  have hz10:z.regs 10=1:=(arun_frame k 10 c.markResetBody (by rfl) p).trans hp10
  dsimp only; by_cases hj:z.regs rJ<c.segLen
  · rcases hlive _ hj with ⟨a,b,d,e,f,g,h⟩
    rw [(c.markAddressBody_live_run k z hz10 hj a b d e f g h).2.2.2.2.1]; omega
  · rw [(c.markAddressBody_exhausted_run k z hz10 hj h7 h8 h9 h10 h11 h12 h13).2.2.2.2.1]; omega

theorem markAddress33_lt_of_markRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState) (hround:s.regs rR<c.markSteps) (hsteps:c.markSteps<M)
    (hlen:13*c.segLen<len)
    (hlive:∀ j,j<c.segLen→j<M∧j+c.segLen<M∧j+2*c.segLen<M∧j+3*c.segLen<M∧j+4*c.segLen<M∧j+5*c.segLen<M∧j+6*c.segLen<M)
    (h7:7*c.segLen<M)(h8:8*c.segLen<M)(h9:9*c.segLen<M)(h10:10*c.segLen<M)
    (h11:11*c.segLen<M)(h12:12*c.segLen<M)(h13:13*c.segLen<M) :
    let p:=arun k s (lift c.markPhaseBody)
    let z:=arun k p c.markResetBody
    (arun k z c.markAddressBody).regs 33<len := by
  let p:=arun k s (lift c.markPhaseBody)
  let z:=arun k p c.markResetBody
  have hp:=c.markPhaseBody_run k s hsteps;dsimp only at hp
  have hp10:p.regs 10=1:=by rw[hp.1,if_pos hround]
  have hz10:z.regs 10=1:=(arun_frame k 10 c.markResetBody (by rfl) p).trans hp10
  dsimp only;by_cases hj:z.regs rJ<c.segLen
  · rcases hlive _ hj with⟨a,b,d,e,f,g,h⟩;rw[(c.markAddressBody_live_run k z hz10 hj a b d e f g h).2.2.2.2.2.1];omega
  · rw[(c.markAddressBody_exhausted_run k z hz10 hj h7 h8 h9 h10 h11 h12 h13).2.2.2.2.2.1];omega

theorem markAddress34_lt_of_markRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hround : s.regs rR < c.markSteps) (hsteps : c.markSteps < M)
    (hlen : 13 * c.segLen < len)
    (hlive : ∀ j, j < c.segLen → j < M ∧ j + c.segLen < M ∧
      j + 2 * c.segLen < M ∧ j + 3 * c.segLen < M ∧ j + 4 * c.segLen < M ∧
      j + 5 * c.segLen < M ∧ j + 6 * c.segLen < M)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let p := arun k s (lift c.markPhaseBody)
    let z := arun k p c.markResetBody
    (arun k z c.markAddressBody).regs 34 < len := by
  let p := arun k s (lift c.markPhaseBody)
  let z := arun k p c.markResetBody
  have hp := c.markPhaseBody_run k s hsteps
  dsimp only at hp
  have hp10 : p.regs 10 = 1 := by rw [hp.1, if_pos hround]
  have hz10 : z.regs 10 = 1 :=
    (arun_frame k 10 c.markResetBody (by rfl) p).trans hp10
  dsimp only
  by_cases hj : z.regs rJ < c.segLen
  · rcases hlive _ hj with ⟨a, b, d, e, f, g, h⟩
    rw [(c.markAddressBody_live_run k z hz10 hj a b d e f g h).2.2.2.2.2.2.1]
    omega
  · rw [(c.markAddressBody_exhausted_run k z hz10 hj h7 h8 h9 h10 h11 h12 h13).2.2.2.2.2.2.1]
    omega

theorem markAddress35_lt_of_markRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hround : s.regs rR < c.markSteps) (hsteps : c.markSteps < M)
    (hlen : 13 * c.segLen < len)
    (hlive : ∀ j, j < c.segLen → j < M ∧ j + c.segLen < M ∧
      j + 2 * c.segLen < M ∧ j + 3 * c.segLen < M ∧ j + 4 * c.segLen < M ∧
      j + 5 * c.segLen < M ∧ j + 6 * c.segLen < M)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let p := arun k s (lift c.markPhaseBody)
    let z := arun k p c.markResetBody
    (arun k z c.markAddressBody).regs 35 < len := by
  let p := arun k s (lift c.markPhaseBody)
  let z := arun k p c.markResetBody
  have hp := c.markPhaseBody_run k s hsteps
  dsimp only at hp
  have hp10 : p.regs 10 = 1 := by rw [hp.1, if_pos hround]
  have hz10 : z.regs 10 = 1 :=
    (arun_frame k 10 c.markResetBody (by rfl) p).trans hp10
  dsimp only
  by_cases hj : z.regs rJ < c.segLen
  · rcases hlive _ hj with ⟨a, b, d, e, f, g, h⟩
    rw [(c.markAddressBody_live_run k z hz10 hj a b d e f g h).2.2.2.2.2.2.2.1]
    omega
  · rw [(c.markAddressBody_exhausted_run k z hz10 hj h7 h8 h9 h10 h11 h12 h13).2.2.2.2.2.2.2.1]
    omega

theorem markAddress36_lt_of_markRound
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState)
    (hround : s.regs rR < c.markSteps) (hsteps : c.markSteps < M)
    (hlen : 13 * c.segLen < len)
    (hlive : ∀ j, j < c.segLen → j < M ∧ j + c.segLen < M ∧
      j + 2 * c.segLen < M ∧ j + 3 * c.segLen < M ∧ j + 4 * c.segLen < M ∧
      j + 5 * c.segLen < M ∧ j + 6 * c.segLen < M)
    (h7 : 7 * c.segLen < M) (h8 : 8 * c.segLen < M)
    (h9 : 9 * c.segLen < M) (h10 : 10 * c.segLen < M)
    (h11 : 11 * c.segLen < M) (h12 : 12 * c.segLen < M)
    (h13 : 13 * c.segLen < M) :
    let p := arun k s (lift c.markPhaseBody)
    let z := arun k p c.markResetBody
    (arun k z c.markAddressBody).regs 36 < len := by
  let p := arun k s (lift c.markPhaseBody)
  let z := arun k p c.markResetBody
  have hp := c.markPhaseBody_run k s hsteps
  dsimp only at hp
  have hp10 : p.regs 10 = 1 := by rw [hp.1, if_pos hround]
  have hz10 : z.regs 10 = 1 :=
    (arun_frame k 10 c.markResetBody (by rfl) p).trans hp10
  dsimp only
  by_cases hj : z.regs rJ < c.segLen
  · rcases hlive _ hj with ⟨a, b, d, e, f, g, h⟩
    rw [(c.markAddressBody_live_run k z hz10 hj a b d e f g h).2.2.2.2.2.2.2.2.1]
    omega
  · rw [(c.markAddressBody_exhausted_run k z hz10 hj h7 h8 h9 h10 h11 h12 h13).2.2.2.2.2.2.2.2.1]
    omega
end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

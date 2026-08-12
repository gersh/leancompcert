import LeanCompCert.Ports.CDEMAbelProductionSieveMark
import LeanCompCert.Ports.CDEMAbelSieveInit

/-! # Production CDEM source-register seed -/

namespace LeanCompCert.Ports.CDEMAbelProductionSourceSeed

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelProductionCertificate

private theorem seedRegs_reg_eq (idx r value : Nat) (s : AState)
    (l : List (Nat × Nat)) (hs : s.regs r = value) (hvalue : value < M)
    (hall : ∀ x ∈ l, x.1 = r → x.2 = value) :
    (arun idx s (seedRegs l)).regs r = value := by
  induction l generalizing s with
  | nil => exact hs
  | cons x xs ih =>
      simp only [seedRegs, List.map_cons, arun]
      apply ih (arun idx s [.scalar (.mov x.1 (.lit x.2))])
      · rw [cdem_seedReg_reg]
        by_cases hx : x.1 = r
        · rw [if_pos hx.symm, hall x (by simp) hx,
            Nat.mod_eq_of_lt hvalue]
        · rw [if_neg (fun h => hx h.symm), hs]
      · intro y hy
        exact hall y (by simp [hy])

private theorem seedRegs_reg_eq_of_mem (idx r value : Nat) (s : AState)
    (l : List (Nat × Nat)) (hvalue : value < M)
    (hmem : (r, value) ∈ l)
    (hall : ∀ x ∈ l, x.1 = r → x.2 = value) :
    (arun idx s (seedRegs l)).regs r = value := by
  induction l generalizing s with
  | nil => simp at hmem
  | cons x xs ih =>
      simp only [seedRegs, List.map_cons, arun]
      by_cases hx : x.1 = r
      · apply seedRegs_reg_eq idx r value
          (arun idx s [.scalar (.mov x.1 (.lit x.2))]) xs
        · rw [cdem_seedReg_reg, if_pos hx.symm,
            hall x (by simp) hx, Nat.mod_eq_of_lt hvalue]
        · exact hvalue
        · intro y hy
          exact hall y (by simp [hy])
      · apply ih (arun idx s [.scalar (.mov x.1 (.lit x.2))])
        · rcases List.mem_cons.mp hmem with hhead | htail
          · exact (hx (Prod.mk.inj hhead).1.symm).elim
          · exact htail
        · intro y hy
          exact hall y (by simp [hy])

private theorem production_seed_reg (r value : Nat) (hvalue : value < M)
    (hmem : (r, value) ∈ productionCfg.seedList)
    (hall : ∀ x ∈ productionCfg.seedList, x.1 = r → x.2 = value) :
    (sieveEntry productionCfg).regs r = value := by
  unfold sieveEntry Cfg.init
  rw [arun_append]
  apply seedRegs_reg_eq_of_mem 0 r value
    (arun 0 initialAState (storeLits productionCfg.primeCells))
    productionCfg.seedList
  · exact hvalue
  · exact hmem
  · exact hall

/-- Exact source-facing registers installed by the physical production
initializer, before either finite scheduled prefix runs. -/
theorem production_source_seed :
    let st := sieveEntry productionCfg
    st.regs rF = 0 ∧ st.regs rE = 0 ∧ st.regs rKr = 0 ∧
      st.regs rC = 0 ∧ st.regs rDp = 0 ∧ st.regs rDn = 0 ∧
      st.regs rT = 1 ∧ st.regs rT2 = 4 ∧
      st.regs rUpLo = 0 ∧ st.regs rUpHi = 0 ∧
      st.regs rUnLo = 0 ∧ st.regs rUnHi = 0 ∧
      st.regs rVLo = 0 ∧ st.regs rVHi = 0 ∧ st.regs rTv = 0 := by
  have zero (r : Nat) (hmem : (r, 0) ∈ productionCfg.seedList)
      (h : ∀ x ∈ productionCfg.seedList, x.1 = r → x.2 = 0) :
      (sieveEntry productionCfg).regs r = 0 :=
    production_seed_reg r 0 (by decide) hmem h
  refine ⟨zero rF (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rF,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rE (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rE,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rKr (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rKr,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rC (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rC,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rDp (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rDp,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rDn (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rDn,
      rW, rD, rSl, rSh, rT, rT2, rK]), ?_, ?_,
    zero rUpLo (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rUpLo,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rUpHi (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rUpHi,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rUnLo (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rUnLo,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rUnHi (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rUnHi,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rVLo (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rVLo,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rVHi (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rVHi,
      rW, rD, rSl, rSh, rT, rT2, rK]),
    zero rTv (by simp [Cfg.seedList]) (by simp [Cfg.seedList, rTv,
      rW, rD, rSl, rSh, rT, rT2, rK])⟩
  · apply production_seed_reg rT 1 (by decide)
    · simp [Cfg.seedList]
    · simp [Cfg.seedList, rZero, rR, rW, rD, rSg, rJ, rN, rPj,
        rM, rPar, rSqf, rF, rE, rKr, rC, rDp, rDn, rSl, rSh, rT,
        rT2, rViol, rUpLo, rUpHi, rUnLo, rUnHi, rVLo, rVHi, rTv, rK]
  · apply production_seed_reg rT2 4 (by decide)
    · simp [Cfg.seedList]
    · simp [Cfg.seedList, rZero, rR, rW, rD, rSg, rJ, rN, rPj,
        rM, rPar, rSqf, rF, rE, rKr, rC, rDp, rDn, rSl, rSh, rT,
        rT2, rViol, rUpLo, rUpHi, rUnLo, rUnHi, rVLo, rVHi, rTv, rK]

/-- The two persistent controls needed to carry the source seed through the
inactive sieve and marking phases. -/
theorem production_source_seed_controls :
    let st := sieveEntry productionCfg
    st.regs rZero = 0 ∧ st.regs rK = 1 := by
  refine ⟨(sieveEntry_seed productionCfg).1, ?_⟩
  apply production_seed_reg rK 1 (by decide)
  · simp [Cfg.seedList]
  · simp [Cfg.seedList, rZero, rR, rW, rD, rSg, rJ, rN, rPj,
      rM, rPar, rSqf, rF, rE, rKr, rC, rDp, rDn, rSl, rSh, rT,
      rT2, rViol, rUpLo, rUpHi, rUnLo, rUnHi, rVLo, rVHi, rTv, rK]

end LeanCompCert.Ports.CDEMAbelProductionSourceSeed

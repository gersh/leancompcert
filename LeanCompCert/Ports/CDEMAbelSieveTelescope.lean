import LeanCompCert.Ports.CDEMAbelSieveStep

/-! # Finite telescope for the CDEM resident Möbius sieve -/

namespace LeanCompCert.Ports.CDEMAbelSieveTelescope

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelPrimitives
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelSieve
open LeanCompCert.Ports.CDEMAbelSievePrefix
open LeanCompCert.Ports.CDEMAbelSieveStep

def writeCell (arr : Nat → Nat) (addr value : Nat) : Nat → Nat :=
  fun j => if j = addr then value else arr j

structure SieveState where
  arr : Nat → Nat
  n : Nat
  pj : Nat
  m : Nat
  par : Nat
  sqf : Nat

def SieveState.row (s : SieveState) : SieveFactorState :=
  let loaded := sieveResetStep s.n s.m s.par s.sqf s.pj s.arr
  sieveFactorStep loaded.toSieveFactorState loaded.p

def SieveState.code (s : SieveState) : Nat :=
  sieveCodeOf s.row.m s.row.par s.row.sqf

def SieveState.step (c : Cfg) (s : SieveState) : SieveState :=
  if s.pj = c.pn - 1 then
    { arr := writeCell s.arr (s.n + c.muBase) s.code
      n := s.n + 1
      pj := 0
      m := s.row.m
      par := s.row.par
      sqf := s.row.sqf }
  else
    { arr := writeCell s.arr c.sink s.code
      n := s.n
      pj := s.pj + 1
      m := s.row.m
      par := s.row.par
      sqf := s.row.sqf }

def SieveState.iter (c : Cfg) : Nat → SieveState → SieveState
  | 0, s => s
  | k + 1, s => (SieveState.iter c k s).step c

def sieveIter (c : Cfg) (idx : Nat) : Nat → AState → AState
  | 0, st => st
  | k + 1, st => arun idx (sieveIter c idx k st) c.sieveBody

structure SieveStateRep (model : SieveState) (machine : AState) : Prop where
  arr : machine.arr = model.arr
  n : machine.regs rN = model.n
  pj : machine.regs rPj = model.pj
  m : machine.regs rM = model.m
  par : machine.regs rPar = model.par
  sqf : machine.regs rSqf = model.sqf
  gate : machine.regs 40 = 1
  zero : machine.regs rZero = 0
  regsWord : ∀ j, machine.regs j < M
  arrWord : ∀ j, machine.arr j < M

structure SieveStepReady (c : Cfg) (s : SieveState) : Prop where
  pjBound : s.pj < c.pn
  primePos : 0 < s.arr s.pj
  pnWord : c.pn < M
  sinkWord : c.sink < M
  addressWord : s.n + c.muBase < M
  nNextWord : s.n + 1 < M
  pjNextWord : s.pj + 1 < M

theorem sieveRowStep_eq (model : SieveState) (machine : AState)
    (h : SieveStateRep model machine) :
    sieveRowStep machine = model.row := by
  unfold sieveRowStep SieveState.row
  rw [h.n, h.m, h.par, h.sqf, h.pj, h.arr]

theorem sieveBody_row_regs (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 1) (hprime : 0 < st.arr (st.regs rPj))
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    let out := arun idx st c.sieveBody
    out.regs rM = (sieveRowStep st).m ∧
      out.regs rPar = (sieveRowStep st).par ∧
      out.regs rSqf = (sieveRowStep st).sqf := by
  let pre := arun idx st (c.sieveBody.take 25)
  have hp := sieveBody_preCode_run c idx st hgate hprime hword harr
  have hsplit : c.sieveBody = c.sieveBody.take 25 ++ c.sieveBody.drop 25 :=
    (List.take_append_drop 25 c.sieveBody).symm
  rw [hsplit, arun_append]
  change (arun idx pre (c.sieveBody.drop 25)).regs rM = _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [show (arun idx pre (c.sieveBody.drop 25)).regs rM = pre.regs rM from
      ArrayRegFrame.arun_frame idx rM (c.sieveBody.drop 25) (by rfl) pre,
      hp.1]
  · rw [show (arun idx pre (c.sieveBody.drop 25)).regs rPar = pre.regs rPar from
      ArrayRegFrame.arun_frame idx rPar (c.sieveBody.drop 25) (by rfl) pre,
      hp.2.1]
  · rw [show (arun idx pre (c.sieveBody.drop 25)).regs rSqf = pre.regs rSqf from
      ArrayRegFrame.arun_frame idx rSqf (c.sieveBody.drop 25) (by rfl) pre,
      hp.2.2.1]

theorem sieveBody_state_step (c : Cfg) (idx : Nat) (machine : AState)
    (model : SieveState) (hrep : SieveStateRep model machine)
    (hready : SieveStepReady c model) :
    SieveStateRep (model.step c) (arun idx machine c.sieveBody) := by
  have hprime : 0 < machine.arr (machine.regs rPj) := by
    rw [hrep.pj, hrep.arr]
    exact hready.primePos
  have hrow := sieveBody_row_regs c idx machine hrep.gate hprime
    hrep.regsWord hrep.arrWord
  have hrowEq := sieveRowStep_eq model machine hrep
  have houtWord := arun_word idx c.sieveBody machine hrep.regsWord hrep.arrWord
  have hgateOut : (arun idx machine c.sieveBody).regs 40 = 1 := by
    rw [show (arun idx machine c.sieveBody).regs 40 = machine.regs 40 from
      ArrayRegFrame.arun_frame idx 40 c.sieveBody (by rfl) machine,
      hrep.gate]
  have hzeroOut : (arun idx machine c.sieveBody).regs rZero = 0 := by
    rw [show (arun idx machine c.sieveBody).regs rZero = machine.regs rZero from
      ArrayRegFrame.arun_frame idx rZero c.sieveBody (by rfl) machine,
      hrep.zero]
  by_cases hlast : model.pj = c.pn - 1
  · have hs := sieveBody_last_model_store c idx machine hrep.gate
      (by rw [hrep.pj, hlast]) hprime hready.pnWord
      (by rw [hrep.n]; exact hready.addressWord)
      (by rw [hrep.n]; exact hready.nNextWord)
      hrep.regsWord hrep.arrWord
    refine
      { arr := ?_
        n := ?_
        pj := ?_
        m := ?_
        par := ?_
        sqf := ?_
        gate := hgateOut
        zero := hzeroOut
        regsWord := houtWord.1
        arrWord := houtWord.2 }
    · funext j
      by_cases hj : j = model.n + c.muBase
      · subst j
        calc
          (arun idx machine c.sieveBody).arr (model.n + c.muBase) =
              (arun idx machine c.sieveBody).arr
                (machine.regs rN + c.muBase) := by rw [hrep.n]
          _ = sieveCodeOf (sieveRowStep machine).m
                (sieveRowStep machine).par (sieveRowStep machine).sqf := hs.1
          _ = (model.step c).arr (model.n + c.muBase) := by
            simp [SieveState.step, hlast, writeCell, SieveState.code, hrowEq]
      · rw [hs.2.1 j (by rw [hrep.n]; exact hj)]
        simp [SieveState.step, hlast, writeCell, hj, hrep.arr]
    · simpa [SieveState.step, hlast, hrep.n] using hs.2.2.2
    · simpa [SieveState.step, hlast] using hs.2.2.1
    · simpa [SieveState.step, hlast, hrowEq] using hrow.1
    · simpa [SieveState.step, hlast, hrowEq] using hrow.2.1
    · simpa [SieveState.step, hlast, hrowEq] using hrow.2.2
  · have hs := sieveBody_nonlast_model c idx machine hrep.gate
      (by rw [hrep.pj]; exact hlast) hprime hready.pnWord hrep.zero
      hready.sinkWord (by rw [hrep.pj]; exact hready.pjNextWord)
      hrep.regsWord hrep.arrWord
    refine
      { arr := ?_
        n := ?_
        pj := ?_
        m := ?_
        par := ?_
        sqf := ?_
        gate := hgateOut
        zero := hzeroOut
        regsWord := houtWord.1
        arrWord := houtWord.2 }
    · funext j
      by_cases hj : j = c.sink
      · subst j
        rw [hs.1]
        simp [SieveState.step, hlast, writeCell, SieveState.code, hrowEq]
      · rw [hs.2.1 j hj]
        simp [SieveState.step, hlast, writeCell, hj, hrep.arr]
    · simpa [SieveState.step, hlast, hrep.n] using hs.2.2.2
    · simpa [SieveState.step, hlast, hrep.pj] using hs.2.2.1
    · simpa [SieveState.step, hlast, hrowEq] using hrow.1
    · simpa [SieveState.step, hlast, hrowEq] using hrow.2.1
    · simpa [SieveState.step, hlast, hrowEq] using hrow.2.2

theorem sieveIter_state_refines (c : Cfg) (idx count : Nat)
    (machine : AState) (model : SieveState)
    (hrep : SieveStateRep model machine)
    (hready : ∀ i, i < count → SieveStepReady c (model.iter c i)) :
    SieveStateRep (model.iter c count) (sieveIter c idx count machine) := by
  induction count with
  | zero => simpa [SieveState.iter, sieveIter] using hrep
  | succ count ih =>
      have hpre := ih (fun i hi => hready i (by omega))
      have hs := sieveBody_state_step c idx (sieveIter c idx count machine)
        (model.iter c count) hpre (hready count (by omega))
      simpa [SieveState.iter, sieveIter] using hs

end LeanCompCert.Ports.CDEMAbelSieveTelescope

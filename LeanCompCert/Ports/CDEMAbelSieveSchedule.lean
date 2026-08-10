import LeanCompCert.Ports.CDEMAbelSieveTable
import LeanCompCert.Ports.CDEMAbelSieveInit
import LeanCompCert.Ports.CDEMAbelMarkSchedule

/-!
# Scheduling the finite CDEM resident sieve

The source program executes the sieve body inside the complete changing-index
loop body.  The inactive marking and accumulation phases still write their
scratch value to `c.sink`; consequently they are not an exact frame of the
whole array.  This file records that effect honestly: after each iteration the
pure sieve state is resynchronised at the scratch sink, while every live cell
and every sieve cursor register remains related to the source step.
-/

namespace LeanCompCert.Ports.CDEMAbelSieveSchedule

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelOuter
open LeanCompCert.Ports.CDEMAbelSieveTelescope
open LeanCompCert.Ports.CDEMAbelSieveReady
open LeanCompCert.Ports.CDEMAbelSieveTable
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelMarkSchedule

/-- The representation needed immediately before the phase selectors run.
Unlike `SieveStateRep`, it does not demand that selector register 40 already
contain one. -/
structure SievePreRep (model : SieveState) (machine : AState) : Prop where
  arr : machine.arr = model.arr
  n : machine.regs rN = model.n
  pj : machine.regs rPj = model.pj
  m : machine.regs rM = model.m
  par : machine.regs rPar = model.par
  sqf : machine.regs rSqf = model.sqf
  zero : machine.regs rZero = 0
  regsWord : ∀ j, machine.regs j < M
  arrWord : ∀ j, machine.arr j < M

def resync (s : SieveState) (machine : AState) : SieveState :=
  { arr := machine.arr
    n := s.n
    pj := s.pj
    m := s.m
    par := s.par
    sqf := s.sqf }

structure SieveSuffixSpec (c : Cfg) (before after : AState) : Prop where
  live : ∀ j, j ≠ c.sink → after.arr j = before.arr j
  n : after.regs rN = before.regs rN
  pj : after.regs rPj = before.regs rPj
  m : after.regs rM = before.regs rM
  par : after.regs rPar = before.regs rPar
  sqf : after.regs rSqf = before.regs rSqf
  sieveGate : after.regs 40 = before.regs 40
  zero : after.regs rZero = before.regs rZero
  regsWord : ∀ j, after.regs j < M
  arrWord : ∀ j, after.arr j < M

def sieveSuffixRun (c : Cfg) (idx : Nat) (st : AState) : AState :=
  arun idx (arun idx (arun idx st c.markBody) c.accBody) c.tailBody

def sieveSuffixBody (c : Cfg) : List AInstr :=
  c.markBody ++ c.accBody ++ c.tailBody

theorem sieveSuffixRun_eq (c : Cfg) (idx : Nat) (st : AState) :
    sieveSuffixRun c idx st = arun idx st (sieveSuffixBody c) := by
  simp [sieveSuffixRun, sieveSuffixBody, arun_append]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem sieveSuffix_run (c : Cfg) (idx : Nat) (st : AState)
    (hmark : st.regs 42 = 0) (hacc : st.regs 43 = 0)
    (hzero : st.regs rZero = 0) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    SieveSuffixSpec c st (sieveSuffixRun c idx st) := by
  let marked := arun idx st c.markBody
  let accumulated := arun idx marked c.accBody
  let out := arun idx accumulated c.tailBody
  have hmarkLive := mark_inactive_live_frame c idx st hmark hsinkM
  have markFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.markBody = false) :
      marked.regs j = st.regs j :=
    ArrayRegFrame.arun_frame idx j c.markBody hwrites st
  have hmarkedAcc : marked.regs 43 = 0 :=
    (markFrame 43 (by rfl)).trans hacc
  have hmarkedZero : marked.regs rZero = 0 :=
    (markFrame rZero (by rfl)).trans hzero
  have hmarkedWord := arun_word idx c.markBody st hword harr
  have haccLive := accBody_inactive_live_frame c idx marked hmarkedAcc
    hmarkedZero hsinkM
  have accFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.accBody = false) :
      accumulated.regs j = marked.regs j :=
    ArrayRegFrame.arun_frame idx j c.accBody hwrites marked
  have haccWord := arun_word idx c.accBody marked hmarkedWord.1 hmarkedWord.2
  have tailFrame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.tailBody = false) :
      out.regs j = accumulated.regs j :=
    ArrayRegFrame.arun_frame idx j c.tailBody hwrites accumulated
  have htailArr : out.arr = accumulated.arr :=
    arun_store_free_arr idx c.tailBody accumulated (by rfl)
  have houtWord := arun_word idx c.tailBody accumulated haccWord.1 haccWord.2
  have field (j : Nat)
      (hwrites : ArrayRegFrame.writes j (sieveSuffixBody c) = false) :
      out.regs j = st.regs j :=
    by
      rw [show out = sieveSuffixRun c idx st by
        rfl, sieveSuffixRun_eq]
      exact ArrayRegFrame.arun_frame idx j (sieveSuffixBody c) hwrites st
  have hall : SieveSuffixSpec c st out :=
    { live := by
        intro j hj
        rw [congrFun htailArr j]
        exact (haccLive j hj).trans (hmarkLive j hj)
      n := field rN (by rfl)
      pj := field rPj (by rfl)
      m := field rM (by rfl)
      par := field rPar (by rfl)
      sqf := field rSqf (by rfl)
      sieveGate := field 40 (by rfl)
      zero := field rZero (by rfl)
      regsWord := houtWord.1
      arrWord := houtWord.2 }
  simpa [sieveSuffixRun, marked, accumulated, out] using hall

theorem body_sieve_split (c : Cfg) :
    c.body = c.selectors ++ c.sieveBody ++ c.markBody ++ c.accBody ++
      c.tailBody :=
  body_mark_split c

set_option maxRecDepth 4096 in
theorem selectors_sieve_rep (c : Cfg) (idx : Nat) (machine : AState)
    (model : SieveState) (hrep : SievePreRep model machine)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hidx : idx < c.sieveLen) :
    let selected := arun idx machine c.selectors
    SieveStateRep model selected ∧ selected.regs 42 = 0 ∧
      selected.regs 43 = 0 := by
  let selected := arun idx machine c.selectors
  have hsel := selectors_sieve_run c idx machine hidxM hsieveM hidx
  change selected.regs 40 = 1 ∧ selected.regs 41 = 0 ∧
      selected.regs 42 = 0 ∧ selected.regs 43 = 0 ∧
      selected.arr = machine.arr at hsel
  have frame (j : Nat)
      (hwrites : ArrayRegFrame.writes j c.selectors = false) :
      selected.regs j = machine.regs j :=
    ArrayRegFrame.arun_frame idx j c.selectors hwrites machine
  have hword := arun_word idx c.selectors machine hrep.regsWord hrep.arrWord
  exact
    ⟨{ arr := hsel.2.2.2.2.trans hrep.arr
       n := (frame rN (by rfl)).trans hrep.n
       pj := (frame rPj (by rfl)).trans hrep.pj
       m := (frame rM (by rfl)).trans hrep.m
       par := (frame rPar (by rfl)).trans hrep.par
       sqf := (frame rSqf (by rfl)).trans hrep.sqf
       gate := hsel.1
       zero := (frame rZero (by rfl)).trans hrep.zero
       regsWord := hword.1
       arrWord := hword.2 },
     hsel.2.2.1, hsel.2.2.2.1⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem sieveCore_finish (c : Cfg) (idx : Nat) (core out : AState)
    (next : SieveState) (hout : out = sieveSuffixRun c idx core)
    (hcore : SieveStateRep next core)
    (hmark : core.regs 42 = 0) (hacc : core.regs 43 = 0)
    (hsinkM : c.sink < M) :
    SievePreRep (resync next out) out ∧
      (∀ j, j ≠ c.sink → out.arr j = next.arr j) := by
  have hsuffix0 := sieveSuffix_run c idx core hmark hacc hcore.zero hsinkM
    hcore.regsWord hcore.arrWord
  have hsuffix : SieveSuffixSpec c core out := by
    rw [hout]
    exact hsuffix0
  have hrep : SievePreRep (resync next out) out :=
    { arr := by rfl
      n := hsuffix.n.trans hcore.n
      pj := hsuffix.pj.trans hcore.pj
      m := hsuffix.m.trans hcore.m
      par := hsuffix.par.trans hcore.par
      sqf := hsuffix.sqf.trans hcore.sqf
      zero := hsuffix.zero.trans hcore.zero
      regsWord := hsuffix.regsWord
      arrWord := hsuffix.arrWord }
  exact ⟨hrep, fun j hj =>
    (hsuffix.live j hj).trans (congrFun hcore.arr j)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem body_sieve_state_step (c : Cfg) (idx : Nat) (machine : AState)
    (model : SieveState) (hrep : SievePreRep model machine)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hidx : idx < c.sieveLen) (hready : SieveStepReady c model)
    (hsinkM : c.sink < M) :
    let out := arun idx machine c.body
    SievePreRep (resync (model.step c) out) out ∧
      (∀ j, j ≠ c.sink → out.arr j = (model.step c).arr j) := by
  let selected := arun idx machine c.selectors
  have hselected := selectors_sieve_rep c idx machine model hrep hidxM
    hsieveM hidx
  change SieveStateRep model selected ∧ selected.regs 42 = 0 ∧
      selected.regs 43 = 0 at hselected
  let core := arun idx selected c.sieveBody
  have hcore := sieveBody_state_step c idx selected model hselected.1 hready
  change SieveStateRep (model.step c) core at hcore
  have hcoreMark : core.regs 42 = 0 := by
    rw [show core.regs 42 = selected.regs 42 from
      ArrayRegFrame.arun_frame idx 42 c.sieveBody (by rfl) selected,
      hselected.2.1]
  have hcoreAcc : core.regs 43 = 0 := by
    rw [show core.regs 43 = selected.regs 43 from
      ArrayRegFrame.arun_frame idx 43 c.sieveBody (by rfl) selected,
      hselected.2.2]
  let out := sieveSuffixRun c idx core
  have hfinished := sieveCore_finish c idx core out (model.step c) rfl hcore
    hcoreMark hcoreAcc hsinkM
  change SievePreRep (resync (model.step c) out) out ∧
      (∀ j, j ≠ c.sink → out.arr j = (model.step c).arr j) at hfinished
  rw [body_sieve_split, arun_append, arun_append, arun_append, arun_append]
  exact hfinished

end LeanCompCert.Ports.CDEMAbelSieveSchedule

import LeanCompCert.Ports.ArraySegMobiusRootMarkFold
import LeanCompCert.Ports.ArraySegMobiusRootPrefix

/-!
# Production-indexed segmented Möbius runs

`bodyRun` is useful for local phase inductions, but it deliberately holds the
loop index fixed.  The emitted `AProgram` supplies the next index to every
iteration.  This file gives that actual finite runner and lifts the generic
root-marking simulation to it.
-/

namespace LeanCompCert.Ports.ArraySegMobiusIndexedRun

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusCursorModel
open LeanCompCert.Ports.ArraySegMobiusScheduleFold
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Ports.ArraySegMobiusRootMarkFold

/-- Actual finite core-body iteration: event `k` sees production index
`idx + k`. -/
def indexedBodyRun (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) : AState :=
  Nat.rec s (fun k q => arun (idx + k) q c.coreBody) fuel

@[simp] theorem indexedBodyRun_zero (idx : Nat) (c : Cfg) (s : AState) :
    indexedBodyRun idx c 0 s = s := rfl

@[simp] theorem indexedBodyRun_succ (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) :
    indexedBodyRun idx c (fuel + 1) s =
      arun (idx + fuel) (indexedBodyRun idx c fuel s) c.coreBody := by
  rfl

/-- Peeling the first indexed event advances the production index for the
remaining suffix. -/
theorem indexedBodyRun_succ_start (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) :
    indexedBodyRun idx c (fuel + 1) s =
      indexedBodyRun (idx + 1) c fuel (arun idx s c.coreBody) := by
  induction fuel with
  | zero => rfl
  | succ k ih =>
      rw [indexedBodyRun_succ]
      rw [ih]
      rw [indexedBodyRun_succ]
      have heq : idx + (k + 1) = idx + 1 + k := by omega
      rw [heq]

/-- Indexed finite runs compose at an arbitrary split point. -/
theorem indexedBodyRun_add (idx : Nat) (c : Cfg) (a b : Nat)
    (s : AState) :
    indexedBodyRun idx c (a + b) s =
      indexedBodyRun (idx + a) c b (indexedBodyRun idx c a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Nat.add_succ, indexedBodyRun_succ, indexedBodyRun_succ, ih]
      have heq : idx + (a + b) = idx + a + b := by omega
      rw [heq]

/-- The production body never writes the distinguished zero register, at
changing indices as well as fixed ones. -/
theorem indexedBodyRun_rZero (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) (hzero : s.regs rZero = 0) :
    (indexedBodyRun idx c fuel s).regs rZero = 0 := by
  induction fuel with
  | zero => exact hzero
  | succ k ih =>
      rw [indexedBodyRun_succ,
        arun_reg_frame (idx + k) rZero c.coreBody _ (by rfl)]
      exact ih

/-- The verified mark counter/window position theorem with the true changing
production index. -/
theorem indexedBodyRun_mark_position (c : Cfg) (idx fuel : Nat)
    (s : AState) (w write : Nat)
    (hfuel : fuel ≤ c.markSteps)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hWrite : s.regs rWrite = write)
    (hLPos : 0 < c.segLen)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxFuelM : idx + fuel < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : ∀ k, k < fuel → idx + k ≠ c.rootSpan - 1)
    (hwriteM : write < M)
    (hwM : w < M) :
    let out := indexedBodyRun idx c fuel s
    out.regs rWrite = write ∧ out.regs rR = fuel ∧
      out.regs rW = w := by
  induction fuel with
  | zero => simpa using And.intro hWrite (And.intro hR hW)
  | succ k ih =>
      have hkLe : k ≤ c.markSteps := by omega
      have hprev := ih hkLe (by omega)
        (fun n hn => hidxNe n (Nat.lt_trans hn (Nat.lt_succ_self k)))
      have hkMark : (indexedBodyRun idx c k s).regs rR < c.markSteps := by
        rw [hprev.2.1]
        omega
      have hone :=
        LeanCompCert.Ports.ArraySegMobiusMark.arun_coreBody_mark_nowrap c
          (idx + k) (indexedBodyRun idx c k s) k w write hkMark
          hprev.2.1 hprev.2.2 hprev.1 hLPos hTM hPM (by omega) hspanM
          (hidxNe k (Nat.lt_succ_self k)) hwriteM hwM
      rw [indexedBodyRun_succ]
      exact hone

/-- Full growing-table representation is framed across an indexed ordinary
marking prefix while the selected-limit cursor supplies branch safety. -/
theorem indexedBodyRun_mark_preserves_tableRep_nonstart
    (c : Cfg) (idx fuel : Nat) (s : AState) (full : List Nat)
    (limit bound w : Nat)
    (hRep : MachineTableRep c s full)
    (hfullLen : full.length ≤ c.tableLen)
    (hready : ∀ k, k < fuel →
      LimitNonstartReady c (indexedBodyRun idx c k s) limit bound w)
    (hmark : ∀ k, k < fuel →
      (indexedBodyRun idx c k s).regs rR < c.markSteps)
    (hlimitLe : limit ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxFuelM : idx + fuel < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : ∀ k, k < fuel → idx + k ≠ c.rootSpan - 1)
    (hLPos : 0 < c.segLen)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hwM : w < M)
    (hA : c.arrayLen < M) :
    MachineTableRep c (indexedBodyRun idx c fuel s) full := by
  induction fuel with
  | zero => simpa using hRep
  | succ k ih =>
      have hk : k < k + 1 := Nat.lt_succ_self k
      rw [indexedBodyRun_succ]
      exact arun_coreBody_mark_preserves_tableRep_nonstart c (idx + k)
        (indexedBodyRun idx c k s) full
        (ih (fun n hn => hready n (Nat.lt_trans hn hk))
          (fun n hn => hmark n (Nat.lt_trans hn hk)) (by omega)
          (fun n hn => hidxNe n (Nat.lt_trans hn hk)))
        hfullLen ((hready k hk).toMain hlimitLe) (hmark k hk)
        htableLenM hTM hPM (by omega) hspanM (hidxNe k hk) hLPos
        hp1Pos hp1M (by rw [(hready k hk).window_eq]; exact hwM) hA

/-- Strong arbitrary-limit marking simulation with the production index
advanced at every event. -/
theorem indexedBodyRun_simulates_limit_nonstart_of_cursor (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat)
    (guard bound w limit i : Nat)
    (hRep : LimitTableRep c s ps guard)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = limit)
    (hcursor0 : CursorMainReady c.segLen w limit bound
      (machineScheduleState c i s).cursor)
    (hR : ∀ k, k < fuel → (indexedBodyRun idx c k s).regs rR ≠ 0)
    (hmark : ∀ k, k < fuel →
      (indexedBodyRun idx c k s).regs rR < c.markSteps)
    (hW : ∀ k, k < fuel →
      (indexedBodyRun idx c k s).regs rW = w)
    (hselectorLimit : ∀ k, k < fuel →
      (arun (idx + k) (indexedBodyRun idx c k s)
        (selectorBlock c)).regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hsegSuccM : c.segLen + 1 < M)
    (hwSegM : w + c.segLen < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    machineScheduleState c i (indexedBodyRun idx c fuel s) =
      scheduleRun fuel c.segLen w limit i
        (fun k => s.arr (c.primeBase + k))
        (machineScheduleState c i s) := by
  let table := fun q => s.arr (c.primeBase + q)
  have htablePrime : ∀ q, q < limit →
      0 < table q ∧ table q ≤ bound := by
    intro q hq
    exact hRep.cell_prime_bounds hInv (by rwa [hpsLen])
  have hguard : 0 < table limit ∧ table limit < M := by
    have heq : table limit = guard := by
      dsimp only [table]
      simpa [hpsLen] using hRep.guard_eq
    rw [heq]
    exact ⟨hRep.guard_pos, hRep.guard_lt_modulus⟩
  have go : ∀ n, n ≤ fuel →
      machineScheduleState c i (indexedBodyRun idx c n s) =
          scheduleRun n c.segLen w limit i table
            (machineScheduleState c i s) ∧
        LimitTableRep c (indexedBodyRun idx c n s) ps guard := by
    intro n hn
    induction n with
    | zero => exact ⟨rfl, hRep⟩
    | succ k ih =>
        have hk : k < fuel := by omega
        have hprev := ih (by omega)
        have hmodelReady := scheduleRun_cursor_main_ready k c.segLen w
          limit bound i table (machineScheduleState c i s) hcursor0
          htablePrime hguard hboundM hsegBoundM hsegSuccM
        have hmachineCursor : CursorMainReady c.segLen w limit bound
            (machineCursor (indexedBodyRun idx c k s)) := by
          change CursorMainReady c.segLen w limit bound
            (machineScheduleState c i (indexedBodyRun idx c k s)).cursor
          rw [hprev.1]
          exact hmodelReady
        have hreadyK := LimitNonstartReady.of_cursor c
          (indexedBodyRun idx c k s) limit bound w hmachineCursor
          (hR k hk) (hW k hk) hboundSqM hsegBoundM hwSegM
        have hone := arun_coreBody_simulates_limit_nonstart c (idx + k)
          (indexedBodyRun idx c k s) ps guard bound w limit hprev.2 hInv
          hpsLen hreadyK (hmark k hk) (hselectorLimit k hk) hlimitLe
          hlimitM hTM hp1Pos hp1M hboundM hA i hi
        have htableK : ∀ q, q ≤ limit →
            (indexedBodyRun idx c k s).arr (c.primeBase + q) =
              table q := by
          intro q hq
          exact hprev.2.same_cell hRep (by rwa [hpsLen])
        have hsimNext :
            machineScheduleState c i
                (arun (idx + k) (indexedBodyRun idx c k s) c.coreBody) =
              scheduleStep c.segLen w limit i table
                (scheduleRun k c.segLen w limit i table
                  (machineScheduleState c i s)) := by
          calc
            machineScheduleState c i
                (arun (idx + k) (indexedBodyRun idx c k s) c.coreBody) =
                scheduleStep c.segLen w limit i
                  (fun q => (indexedBodyRun idx c k s).arr
                    (c.primeBase + q))
                  (machineScheduleState c i
                    (indexedBodyRun idx c k s)) := hone
            _ = scheduleStep c.segLen w limit i table
                  (machineScheduleState c i
                    (indexedBodyRun idx c k s)) :=
              scheduleStep_table_congr c.segLen w limit i _ _ _ htableK
            _ = scheduleStep c.segLen w limit i table
                  (scheduleRun k c.segLen w limit i table
                    (machineScheduleState c i s)) := by rw [hprev.1]
        have hRepNext :=
          arun_coreBody_mark_preserves_limitTableRep_nonstart c (idx + k)
            (indexedBodyRun idx c k s) ps guard limit bound w hprev.2
            hpsLen hreadyK (hmark k hk) hlimitLe hlimitM hTM hp1Pos
            hp1M hA
        constructor
        · rw [indexedBodyRun_succ, scheduleRun_succ]
          exact hsimNext
        · rw [indexedBodyRun_succ]
          exact hRepNext
  exact (go fuel (Nat.le_refl _)).1

/-- Complete root marking simulation for the true production indices.  The
index-range premise keeps every marking event strictly before the special
last-root transition body. -/
theorem indexedBodyRun_simulates_root_from_start (c : Cfg)
    (idx fuel : Nat) (s : AState) (boot : List Nat)
    (guard bound w i : Nat)
    (hRep : LimitTableRep c s boot guard)
    (hInv : PrimeTableInv boot bound)
    (hbootLen : boot.length = c.bootCount)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hfuel : fuel + 1 ≤ c.markSteps)
    (hrootMark : idx + (fuel + 1) ≤ c.rootSpan - 1)
    (hbootPos : 0 < c.bootCount)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    let first := arun idx s c.coreBody
    machineScheduleState c i (indexedBodyRun idx c (fuel + 1) s) =
      scheduleRun fuel c.segLen w c.bootCount i
        (fun k => first.arr (c.primeBase + k))
        (scheduleStart c.segLen w c.firstPrime i (machineCell c s i)) := by
  let first := arun idx s c.coreBody
  have hTPos : 0 < c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hsegSuccM : c.segLen + 1 < M := by omega
  have hwM : w < M := by omega
  have hidxRoot : idx < c.rootSpan := by omega
  have hidxM : idx < M := by omega
  have hstartPair := arun_coreBody_simulates_start c idx s w c.bootCount
    hR hW
    (selectorBlock_limit_root c idx s hidxRoot hidxM hspanM hbootLe
      htableLenM).1
    hbootLe (by omega) hTPos hTM hp1Pos hp1LeL hp1M hp1SqM hnStartM
    hA i hi
  have hstartEq : machineScheduleState c i first =
      scheduleStart c.segLen w c.firstPrime i (machineCell c s i) := by
    exact ScheduleState.ext hstartPair.1 hstartPair.2
  have hRepFirst :=
    arun_coreBody_mark_preserves_limitTableRep_start c idx s boot guard
      c.bootCount hRep hbootLen hR hTPos hTM hp1Pos hp1LeL hp1M hp1SqM
      (by rw [hW]; exact hnStartM) hA hbootLe
  have hcursorFirst : CursorMainReady c.segLen w c.bootCount bound
      (machineScheduleState c i first).cursor := by
    rw [hstartEq]
    exact scheduleStart_cursor_ready c.segLen w c.bootCount bound
      c.firstPrime i (machineCell c s i) hbootPos hp1Pos hp1LeL
      hp1LeBound hboundM hsegBoundM
  have hposition (n : Nat) (hn : n ≤ fuel + 1) :
      (indexedBodyRun idx c n s).regs rWrite = s.regs rWrite ∧
        (indexedBodyRun idx c n s).regs rR = n ∧
        (indexedBodyRun idx c n s).regs rW = w :=
    indexedBodyRun_mark_position c idx n s w (s.regs rWrite) (by omega)
      hR hW rfl hLPos hTM hPM (by omega) hspanM
      (fun k hk => by omega) hwriteM hwM
  have hpositionFirst (k : Nat) (hk : k ≤ fuel) :
      (indexedBodyRun (idx + 1) c k first).regs rWrite =
          s.regs rWrite ∧
        (indexedBodyRun (idx + 1) c k first).regs rR = k + 1 ∧
        (indexedBodyRun (idx + 1) c k first).regs rW = w := by
    have hp := hposition (k + 1) (by omega)
    rw [indexedBodyRun_succ_start] at hp
    simpa [first, Nat.add_comm] using hp
  have hsim := indexedBodyRun_simulates_limit_nonstart_of_cursor c
    (idx + 1) fuel first boot guard bound w c.bootCount i hRepFirst hInv
    hbootLen hcursorFirst
    (fun k hk => by rw [(hpositionFirst k (by omega)).2.1]; omega)
    (fun k hk => by rw [(hpositionFirst k (by omega)).2.1]; omega)
    (fun k hk => (hpositionFirst k (by omega)).2.2)
    (fun k hk => by
      have hcurRoot : idx + 1 + k < c.rootSpan := by omega
      have hcurM : idx + 1 + k < M := by omega
      exact (selectorBlock_limit_root c (idx + 1 + k)
        (indexedBodyRun (idx + 1) c k first) hcurRoot hcurM hspanM
        hbootLe htableLenM).1)
    hbootLe (by omega) hTM hp1Pos hp1M hboundM hboundSqM hsegBoundM
    hsegSuccM hwSegM hA hi
  rw [indexedBodyRun_succ_start]
  exact hsim.trans (by rw [hstartEq])

/-- The same changing-index root marking run frames the complete growing
prime table, even though its selector traverses only the bootstrap prefix. -/
theorem indexedBodyRun_root_mark_preserves_full_table (c : Cfg)
    (idx fuel : Nat) (s : AState) (full boot : List Nat)
    (guard bound w i : Nat)
    (hFull : MachineTableRep c s full)
    (hfullLen : full.length ≤ c.tableLen)
    (hRep : LimitTableRep c s boot guard)
    (hInv : PrimeTableInv boot bound)
    (hbootLen : boot.length = c.bootCount)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hfuel : fuel + 1 ≤ c.markSteps)
    (hrootMark : idx + (fuel + 1) ≤ c.rootSpan - 1)
    (hbootPos : 0 < c.bootCount)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M) (hi : i < c.segLen) :
    MachineTableRep c (indexedBodyRun idx c (fuel + 1) s) full ∧
      LimitTableRep c (indexedBodyRun idx c (fuel + 1) s) boot guard := by
  let first := arun idx s c.coreBody
  have hTPos : 0 < c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hsegSuccM : c.segLen + 1 < M := by omega
  have hwM : w < M := by omega
  have hidxRoot : idx < c.rootSpan := by omega
  have hidxM : idx < M := by omega
  have hFullFirst : MachineTableRep c first full := by
    dsimp only [first]
    exact arun_coreBody_mark_preserves_tableRep_start c idx s full hFull
      hfullLen hR hTPos hTM hPM hidxM hspanM (by omega) hLPos hp1Pos
      hp1LeL hp1M hp1SqM (by rw [hW]; exact hnStartM)
      (by rw [hW]; exact hwM) hA
  have hRepFirst : LimitTableRep c first boot guard :=
    arun_coreBody_mark_preserves_limitTableRep_start c idx s boot guard
      c.bootCount hRep hbootLen hR hTPos hTM hp1Pos hp1LeL hp1M hp1SqM
      (by rw [hW]; exact hnStartM) hA hbootLe
  have hstartPair := arun_coreBody_simulates_start c idx s w c.bootCount
    hR hW
    (selectorBlock_limit_root c idx s hidxRoot hidxM hspanM hbootLe
      htableLenM).1
    hbootLe (by omega) hTPos hTM hp1Pos hp1LeL hp1M hp1SqM hnStartM
    hA i hi
  have hstartEq : machineScheduleState c i first =
      scheduleStart c.segLen w c.firstPrime i (machineCell c s i) :=
    ScheduleState.ext hstartPair.1 hstartPair.2
  have hcursorFirst : CursorMainReady c.segLen w c.bootCount bound
      (machineScheduleState c i first).cursor := by
    rw [hstartEq]
    exact scheduleStart_cursor_ready c.segLen w c.bootCount bound
      c.firstPrime i (machineCell c s i) hbootPos hp1Pos hp1LeL
      hp1LeBound hboundM hsegBoundM
  have hposition (n : Nat) (hn : n ≤ fuel + 1) :
      (indexedBodyRun idx c n s).regs rWrite = s.regs rWrite ∧
        (indexedBodyRun idx c n s).regs rR = n ∧
        (indexedBodyRun idx c n s).regs rW = w :=
    indexedBodyRun_mark_position c idx n s w (s.regs rWrite) (by omega)
      hR hW rfl hLPos hTM hPM (by omega) hspanM
      (fun k hk => by omega) hwriteM hwM
  have hpositionFirst (k : Nat) (hk : k ≤ fuel) :
      (indexedBodyRun (idx + 1) c k first).regs rWrite = s.regs rWrite ∧
        (indexedBodyRun (idx + 1) c k first).regs rR = k + 1 ∧
        (indexedBodyRun (idx + 1) c k first).regs rW = w := by
    have hp := hposition (k + 1) (by omega)
    rw [indexedBodyRun_succ_start] at hp
    simpa [first, Nat.add_comm] using hp
  let table := fun q => first.arr (c.primeBase + q)
  have htablePrime : ∀ q, q < c.bootCount →
      0 < table q ∧ table q ≤ bound := by
    intro q hq
    exact hRepFirst.cell_prime_bounds hInv (by rwa [hbootLen])
  have hguard : 0 < table c.bootCount ∧ table c.bootCount < M := by
    have heq : table c.bootCount = guard := by
      dsimp only [table]
      simpa [hbootLen] using hRepFirst.guard_eq
    rw [heq]
    exact ⟨hRepFirst.guard_pos, hRepFirst.guard_lt_modulus⟩
  have hready : ∀ k, k < fuel →
      LimitNonstartReady c (indexedBodyRun (idx + 1) c k first)
        c.bootCount bound w := by
    intro k hk
    have hsim := indexedBodyRun_simulates_limit_nonstart_of_cursor c
      (idx + 1) k first boot guard bound w c.bootCount i hRepFirst hInv
      hbootLen hcursorFirst
      (fun n hn => by rw [(hpositionFirst n (by omega)).2.1]; omega)
      (fun n hn => by rw [(hpositionFirst n (by omega)).2.1]; omega)
      (fun n hn => (hpositionFirst n (by omega)).2.2)
      (fun n hn =>
        (selectorBlock_limit_root c (idx + 1 + n)
          (indexedBodyRun (idx + 1) c n first) (by omega) (by omega)
          hspanM hbootLe htableLenM).1)
      hbootLe (by omega) hTM hp1Pos hp1M hboundM hboundSqM
      hsegBoundM hsegSuccM hwSegM hA hi
    have hmodelReady := scheduleRun_cursor_main_ready k c.segLen w
      c.bootCount bound i table (machineScheduleState c i first)
      hcursorFirst htablePrime hguard hboundM hsegBoundM hsegSuccM
    have hmachineCursor : CursorMainReady c.segLen w c.bootCount bound
        (machineCursor (indexedBodyRun (idx + 1) c k first)) := by
      change CursorMainReady c.segLen w c.bootCount bound
        (machineScheduleState c i
          (indexedBodyRun (idx + 1) c k first)).cursor
      rw [hsim]
      exact hmodelReady
    exact LimitNonstartReady.of_cursor c
      (indexedBodyRun (idx + 1) c k first) c.bootCount bound w
      hmachineCursor (by rw [(hpositionFirst k (by omega)).2.1]; omega)
      (hpositionFirst k (by omega)).2.2 hboundSqM hsegBoundM hwSegM
  have hrest := indexedBodyRun_mark_preserves_tableRep_nonstart c
    (idx + 1) fuel first full c.bootCount bound w hFullFirst hfullLen
    hready (fun k hk => by rw [(hpositionFirst k (by omega)).2.1]; omega)
    hbootLe htableLenM hTM hPM (by omega) hspanM
    (fun k hk => by omega) hLPos hp1Pos hp1M hwM hA
  have hlimitGo : ∀ n, n ≤ fuel → LimitTableRep c
      (indexedBodyRun (idx + 1) c n first) boot guard := by
    intro n hn
    induction n with
    | zero => simpa using hRepFirst
    | succ k ih =>
        rw [indexedBodyRun_succ]
        exact arun_coreBody_mark_preserves_limitTableRep_nonstart c
          (idx + 1 + k) (indexedBodyRun (idx + 1) c k first) boot guard
          c.bootCount bound w (ih (by omega)) hbootLen
          (hready k (by omega))
          (by rw [(hpositionFirst k (by omega)).2.1]; omega) hbootLe
          (by omega) hTM hp1Pos hp1M hA
  have hlimitRest := hlimitGo fuel (Nat.le_refl _)
  rw [indexedBodyRun_succ_start]
  exact ⟨hrest, hlimitRest⟩

/-- Complete indexed root marking computes the finite bootstrap fold. -/
theorem indexedBodyRun_root_cell_eq_rootCellFoldFrom
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (guard bound w i : Nat)
    (hRep : LimitTableRep c s (c.firstPrime :: ps) guard)
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hbootLen : (c.firstPrime :: ps).length = c.bootCount)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hrootMark : idx + c.markSteps ≤ c.rootSpan - 1)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen) :
    machineCell c (indexedBodyRun idx c c.markSteps s) i =
      rootCellFoldFrom (w + i) (machineCell c s i)
        (c.firstPrime :: ps) := by
  let first := arun idx s c.coreBody
  have hsumPos : 0 <
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum := by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0 < 2)) _
  have hTPos : 0 < c.markSteps := Nat.lt_of_lt_of_le hsumPos hbudget
  have hbootPos : 0 < c.bootCount := by
    rw [← hbootLen]
    simp
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hRepFirst : LimitTableRep c first (c.firstPrime :: ps) guard := by
    dsimp only [first]
    exact arun_coreBody_mark_preserves_limitTableRep_start c idx s
      (c.firstPrime :: ps) guard c.bootCount hRep hbootLen hR hTPos hTM
      hp1Pos hp1LeL hp1M hp1SqM (by rw [hW]; exact hnStartM) hA
      hbootLe
  have hsim := indexedBodyRun_simulates_root_from_start c idx
    (c.markSteps - 1) s (c.firstPrime :: ps) guard bound w i hRep hInv
    hbootLen hR hW (by omega) (by omega) hbootPos hbootLe htableLenM
    hTM hPM hspanM hwriteM hp1Pos hp1LeL hp1LeBound hboundM
    hboundSqM hsegBoundM hwSegM hnStartM hA hi
  have hsteps : c.markSteps - 1 + 1 = c.markSteps := by omega
  rw [hsteps] at hsim
  exact machineCell_eq_rootCellFoldFrom_of_limit_schedule c first
    (indexedBodyRun idx c c.markSteps s) (machineCell c s i) ps guard
    bound w c.bootCount i hRepFirst hInv hbootLen hp1LeL hbudget hi hsim

/-- Cleared-cell specialization of the indexed root marking theorem. -/
theorem indexedBodyRun_root_cell_eq_rootCellFold
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (guard bound w i : Nat)
    (hRep : LimitTableRep c s (c.firstPrime :: ps) guard)
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hbootLen : (c.firstPrime :: ps).length = c.bootCount)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hrootMark : idx + c.markSteps ≤ c.rootSpan - 1)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hspanM : c.rootSpan < M)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen)
    (hclear : machineCell c s i = ⟨0, 0⟩) :
    machineCell c (indexedBodyRun idx c c.markSteps s) i =
      rootCellFold (c.firstPrime :: ps) (w + i) := by
  rw [indexedBodyRun_root_cell_eq_rootCellFoldFrom c idx s ps guard bound
    w i hRep hInv hbootLen hR hW hrootMark hbootLe htableLenM hTM hPM
    hspanM hwriteM hp1Pos hp1LeL hp1LeBound hboundM hboundSqM
    hsegBoundM hwSegM hnStartM hA hbudget hi, hclear]
  rfl

end LeanCompCert.Ports.ArraySegMobiusIndexedRun

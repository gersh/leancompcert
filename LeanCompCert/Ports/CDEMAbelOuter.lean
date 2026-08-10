import LeanCompCert.Ports.CDEMAbelSchedule

namespace LeanCompCert.Ports.CDEMAbelOuter

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelBody

def selectorsS (c : Cfg) : List Instr :=
  [ .binop 40 .lt .idx (.lit c.sieveLen)
  , .binop 41 .sub (.lit 1) (.reg 40)
  , .binop 42 .lt (.reg rR) (.lit c.markSteps)
  , .binop 42 .mul (.reg 42) (.reg 41)
  , .binop 43 .sub (.reg 41) (.reg 42) ]

theorem selectors_lift (c : Cfg) : c.selectors = lift (selectorsS c) := rfl

theorem selectors_acc_run (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR) :
    let out := arun idx st c.selectors
    out.regs 40 = 0 ∧ out.regs 41 = 1 ∧ out.regs 42 = 0 ∧
      out.regs 43 = 1 ∧ out.arr = st.arr := by
  rw [selectors_lift, arun_lift]
  have hidxmod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hsievemod : c.sieveLen % M = c.sieveLen := Nat.mod_eq_of_lt hsieveM
  have hmarkmod : c.markSteps % M = c.markSteps := Nat.mod_eq_of_lt hmarkM
  have hnotS : ¬idx < c.sieveLen := Nat.not_lt.mpr hsieve
  have hnotM : ¬st.regs rR < c.markSteps := Nat.not_lt.mpr hR
  have hnotM' : ¬st.regs 2 < c.markSteps := by simpa [rR] using hnotM
  have h1M : (1 : Nat) % M = 1 := by decide
  have hwrap1 : (1 + M) % M = 1 := by decide
  simp [selectorsS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rR, hidxmod, hsievemod, hmarkmod, hnotS, hnotM', h1M, hwrap1]

def sieveInactiveSuffix (c : Cfg) : List AInstr :=
  [ .scalar (.binop 64 .mul (.reg 64) (.reg 40))
  , .scalar (.binop 65 .add (.reg rN) (.lit c.muBase)) ] ++
    muxBody 66 64 65 rZero 67 ++
  [ .scalar (.binop 68 .sub (.lit 1) (.reg 64))
  , .scalar (.binop 69 .mul (.reg 68) (.lit c.sink))
  , .scalar (.binop 66 .add (.reg 66) (.reg 69))
  , .store 66 63
  , .scalar (.binop 70 .add (.reg rPj) (.reg 40))
  , .scalar (.binop 71 .sub (.lit 1) (.reg 64))
  , .scalar (.binop rPj .mul (.reg 70) (.reg 71))
  , .scalar (.binop rN .add (.reg rN) (.reg 64)) ]

theorem sieveBody_inactive_split (c : Cfg) :
    c.sieveBody = c.sieveBody.take 30 ++ sieveInactiveSuffix c := by
  simp [Cfg.sieveBody, sieveInactiveSuffix, muxBody]

def avoidsStore : AInstr → Bool
  | .store _ _ => false
  | _ => true

theorem arun_store_free_arr (idx : Nat) : ∀ (l : List AInstr) (st : AState),
    l.all avoidsStore = true → (arun idx st l).arr = st.arr := by
  intro l
  induction l with
  | nil => intro st _; rfl
  | cons i rest ih =>
      intro st h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => exact AState.writeReg_arr _ _ _
      | load dest address => exact AState.writeReg_arr _ _ _
      | store address value => simp [avoidsStore] at h

theorem sieve_inactive_live_frame (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 40 = 0) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) :
    ∀ j, j ≠ c.sink →
      (arun idx st c.sieveBody).arr j = st.arr j := by
  intro j hj
  let pre := arun idx st (c.sieveBody.take 30)
  have hgatePre : pre.regs 40 = 0 := by
    rw [show pre.regs 40 = st.regs 40 from
      ArrayRegFrame.arun_frame idx 40 (c.sieveBody.take 30) (by rfl) st,
      hgate]
  have hzeroPre : pre.regs rZero = 0 := by
    rw [show pre.regs rZero = st.regs rZero from
      ArrayRegFrame.arun_frame idx rZero (c.sieveBody.take 30) (by rfl) st,
      hzero]
  have hzeroPre1 : pre.regs 1 = 0 := by simpa [rZero] using hzeroPre
  have harrPre : pre.arr = st.arr := by
    exact arun_store_free_arr idx (c.sieveBody.take 30) st (by rfl)
  have hsinkMod : c.sink % M = c.sink := Nat.mod_eq_of_lt hsinkM
  rw [sieveBody_inactive_split, arun_append]
  change (arun idx pre (sieveInactiveSuffix c)).arr j = st.arr j
  simp [sieveInactiveSuffix, muxBody, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
    AState.writeArr, rZero, rN, rPj, hgatePre, hzeroPre1, hsinkMod, hj,
    harrPre]

def markInactiveStoreBlock (c : Cfg) : List AInstr :=
  [ .scalar (.binop 82 .mul (.reg 82) (.reg 42))
  , .scalar (.binop 83 .mul (.reg 82) (.reg rJ))
  , .scalar (.binop 84 .sub (.lit 1) (.reg 82))
  , .scalar (.binop 85 .mul (.reg 84) (.lit c.sink))
  , .scalar (.binop 86 .mul (.reg 82) (.lit c.winBase))
  , .scalar (.binop 83 .add (.reg 83) (.reg 86))
  , .scalar (.binop 83 .add (.reg 83) (.reg 85))
  , .load 87 83
  , .scalar (.binop 88 .mul (.reg 82) (.reg rSg))
  , .scalar (.binop 87 .add (.reg 87) (.reg 88))
  , .store 83 87 ]

theorem markBody_inactive_split (c : Cfg) :
    c.markBody = c.markBody.take 21 ++ markInactiveStoreBlock c ++
      c.markBody.drop 32 := by
  simp [Cfg.markBody, markInactiveStoreBlock, muxBody]

theorem mark_inactive_live_frame (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 42 = 0) (hsinkM : c.sink < M) :
    ∀ j, j ≠ c.sink → (arun idx st c.markBody).arr j = st.arr j := by
  intro j hj
  let pre := arun idx st (c.markBody.take 21)
  let stored := arun idx pre (markInactiveStoreBlock c)
  have hgatePre : pre.regs 42 = 0 := by
    rw [show pre.regs 42 = st.regs 42 from
      ArrayRegFrame.arun_frame idx 42 (c.markBody.take 21) (by rfl) st,
      hgate]
  have harrPre : pre.arr = st.arr :=
    arun_store_free_arr idx (c.markBody.take 21) st (by rfl)
  have hsinkMod : c.sink % M = c.sink := Nat.mod_eq_of_lt hsinkM
  have hstored : stored.arr j = st.arr j := by
    simp [stored, markInactiveStoreBlock, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      AState.writeArr, rJ, rSg, hgatePre, hsinkMod, hj, harrPre]
  have htail : (arun idx stored (c.markBody.drop 32)).arr = stored.arr :=
    arun_store_free_arr idx (c.markBody.drop 32) stored (by rfl)
  rw [markBody_inactive_split, arun_append, arun_append]
  exact (congrFun htail j).trans hstored

set_option maxRecDepth 4096 in
theorem mark_inactive_cell_frame (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 41 = 1) (hmarkPos : 0 < c.markSteps)
    (hR : c.markSteps ≤ st.regs rR) (hword : ∀ j, st.regs j < M) :
    (arun idx st c.markBody).regs rC = st.regs rC := by
  let pre := arun idx st (c.markBody.take 21)
  have hRne : st.regs rR ≠ 0 := by omega
  have hRne2 : st.regs 2 ≠ 0 := by simpa [rR] using hRne
  have hCmod : st.regs 15 % M = st.regs 15 := by
    exact Nat.mod_eq_of_lt (by simpa [rC] using hword rC)
  have hpre : pre.regs rC = st.regs rC := by
    simp [pre, Cfg.markBody, muxBody, arun, astep, InstrBlock.sdest,
      InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
      rZero, rR, rC, rD, rSg, rJ, hgate, hRne2, hCmod]
  have htail : (arun idx pre (c.markBody.drop 21)).regs rC = pre.regs rC :=
    ArrayRegFrame.arun_frame idx rC (c.markBody.drop 21) (by rfl) pre
  rw [← List.take_append_drop 21 c.markBody, arun_append]
  exact htail.trans hpre

def markViolationSuffix (c : Cfg) : List AInstr :=
  [ .scalar (.binop 134 .eq (.reg rR) (.lit (c.markSteps - 1)))
  , .scalar (.binop 134 .mul (.reg 134) (.reg 41))
  , .scalar (.binop 135 .lt (.reg rD) (.lit c.kBound))
  , .scalar (.binop 134 .mul (.reg 134) (.reg 135))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 134))
  , .scalar (.binop rVMark .add (.reg rVMark) (.reg 134)) ]

theorem markBody_violation_split (c : Cfg) :
    c.markBody = c.markBody.take 68 ++ markViolationSuffix c := by
  simp [Cfg.markBody, markViolationSuffix, muxBody]

theorem mark_inactive_violation_frame (c : Cfg) (idx : Nat) (st : AState)
    (hmarkPos : 0 < c.markSteps) (hmarkM : c.markSteps < M)
    (hR : c.markSteps ≤ st.regs rR)
    (hword : ∀ j, st.regs j < M) :
    let out := arun idx st c.markBody
    out.regs rViol = st.regs rViol ∧ out.regs rVMark = st.regs rVMark := by
  let pre := arun idx st (c.markBody.take 68)
  have preR : pre.regs rR = st.regs rR :=
    ArrayRegFrame.arun_frame idx rR (c.markBody.take 68) (by rfl) st
  have preViol : pre.regs rViol = st.regs rViol :=
    ArrayRegFrame.arun_frame idx rViol (c.markBody.take 68) (by rfl) st
  have preVMark : pre.regs rVMark = st.regs rVMark :=
    ArrayRegFrame.arun_frame idx rVMark (c.markBody.take 68) (by rfl) st
  have hne : pre.regs rR ≠ c.markSteps - 1 := by rw [preR]; omega
  have hsubMod : (c.markSteps - 1) % M = c.markSteps - 1 := by
    exact Nat.mod_eq_of_lt (by omega)
  have hne2 : pre.regs 2 ≠ (c.markSteps - 1) % M := by
    simpa [rR, hsubMod] using hne
  have hviolMod : pre.regs rViol % M = pre.regs rViol := by
    rw [preViol]
    exact Nat.mod_eq_of_lt (hword rViol)
  have hvmarkMod : pre.regs rVMark % M = pre.regs rVMark := by
    rw [preVMark]
    exact Nat.mod_eq_of_lt (hword rVMark)
  have preViol22 : pre.regs 22 = st.regs 22 := by
    simpa [rViol] using preViol
  have preVMark246 : pre.regs 246 = st.regs 246 := by
    simpa [rVMark] using preVMark
  have hviolMod22 : pre.regs 22 % M = pre.regs 22 := by
    simpa [rViol] using hviolMod
  have hvmarkMod246 : pre.regs 246 % M = pre.regs 246 := by
    simpa [rVMark] using hvmarkMod
  have hneRun : (arun idx st (c.markBody.take 68)).regs 2 ≠
      c.markSteps - 1 := by simpa [pre, rR] using hne
  have preViolRun : (arun idx st (c.markBody.take 68)).regs 22 =
      st.regs 22 := by simpa [pre, rViol] using preViol
  have preVMarkRun : (arun idx st (c.markBody.take 68)).regs 246 =
      st.regs 246 := by simpa [pre, rVMark] using preVMark
  have hstViolMod : st.regs 22 % M = st.regs 22 := by
    exact Nat.mod_eq_of_lt (by simpa [rViol] using hword rViol)
  have hstVMarkMod : st.regs 246 % M = st.regs 246 := by
    exact Nat.mod_eq_of_lt (by simpa [rVMark] using hword rVMark)
  rw [markBody_violation_split, arun_append]
  simp [markViolationSuffix, arun, astep, InstrBlock.sdest,
    InstrBlock.sval, denoteOperand, denoteOp, AState.writeReg,
    rR, rD, rViol, rVMark, hneRun, hsubMod,
    preViolRun, preVMarkRun, hstViolMod, hstVMarkMod]

def accPrefix (c : Cfg) : List AInstr :=
  c.selectors ++ c.sieveBody ++ c.markBody

structure AccPrefixLatchSpec (before after : AState) : Prop where
  gate : after.regs 43 = 1
  zero : after.regs rZero = before.regs rZero
  key : after.regs rK = before.regs rK
  dPos : after.regs rDp = before.regs rDp
  dNeg : after.regs rDn = before.regs rDn
  round : after.regs rKr = before.regs rKr
  low : after.regs rSl = before.regs rSl
  high : after.regs rSh = before.regs rSh
  cell : after.regs rC = before.regs rC
  viol : after.regs rViol = before.regs rViol
  vMark : after.regs rVMark = before.regs rVMark

theorem accPrefix_latches (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hmarkPos : 0 < c.markSteps) (hR : c.markSteps ≤ st.regs rR)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    AccPrefixLatchSpec st (arun idx st (accPrefix c)) := by
  let selected := arun idx st c.selectors
  let sieved := arun idx selected c.sieveBody
  let marked := arun idx sieved c.markBody
  have hsel := selectors_acc_run c idx st hidxM hsieveM hsieve hmarkM hR
  dsimp only at hsel
  have hsieved41 : sieved.regs 41 = 1 := by
    rw [show sieved.regs 41 = selected.regs 41 from
      ArrayRegFrame.arun_frame idx 41 c.sieveBody (by rfl) selected,
      hsel.2.1]
  have hsievedR : sieved.regs rR = st.regs rR := by
    rw [show sieved.regs rR = selected.regs rR from
      ArrayRegFrame.arun_frame idx rR c.sieveBody (by rfl) selected,
      show selected.regs rR = st.regs rR from
        ArrayRegFrame.arun_frame idx rR c.selectors (by rfl) st]
  have hwSelected := arun_word idx c.selectors st hword harrword
  have hwSieved := arun_word idx c.sieveBody selected hwSelected.1 hwSelected.2
  have hcellMarked : marked.regs rC = sieved.regs rC :=
    mark_inactive_cell_frame c idx sieved hsieved41 hmarkPos
      (by rw [hsievedR]; exact hR) hwSieved.1
  have hviolMarked := mark_inactive_violation_frame c idx sieved hmarkPos
    hmarkM (by rw [hsievedR]; exact hR) hwSieved.1
  dsimp only at hviolMarked
  have hcellSieved : sieved.regs rC = st.regs rC := by
    rw [show sieved.regs rC = selected.regs rC from
      ArrayRegFrame.arun_frame idx rC c.sieveBody (by rfl) selected,
      show selected.regs rC = st.regs rC from
        ArrayRegFrame.arun_frame idx rC c.selectors (by rfl) st]
  have hviolSieved : sieved.regs rViol = st.regs rViol := by
    rw [show sieved.regs rViol = selected.regs rViol from
      ArrayRegFrame.arun_frame idx rViol c.sieveBody (by rfl) selected,
      show selected.regs rViol = st.regs rViol from
        ArrayRegFrame.arun_frame idx rViol c.selectors (by rfl) st]
  have hvmarkSieved : sieved.regs rVMark = st.regs rVMark := by
    rw [show sieved.regs rVMark = selected.regs rVMark from
      ArrayRegFrame.arun_frame idx rVMark c.sieveBody (by rfl) selected,
      show selected.regs rVMark = st.regs rVMark from
        ArrayRegFrame.arun_frame idx rVMark c.selectors (by rfl) st]
  have frame (j : Nat) (hw : ArrayRegFrame.writes j (accPrefix c) = false) :
      (arun idx st (accPrefix c)).regs j = st.regs j :=
    ArrayRegFrame.arun_frame idx j (accPrefix c) hw st
  have hall : AccPrefixLatchSpec st marked :=
    { gate := by
        rw [show marked.regs 43 = sieved.regs 43 from
          ArrayRegFrame.arun_frame idx 43 c.markBody (by rfl) sieved,
          show sieved.regs 43 = selected.regs 43 from
            ArrayRegFrame.arun_frame idx 43 c.sieveBody (by rfl) selected,
          hsel.2.2.2.1]
      zero := frame rZero (by rfl)
      key := frame rK (by rfl)
      dPos := frame rDp (by rfl)
      dNeg := frame rDn (by rfl)
      round := frame rKr (by rfl)
      low := frame rSl (by rfl)
      high := frame rSh (by rfl)
      cell := hcellMarked.trans hcellSieved
      viol := hviolMarked.1.trans hviolSieved
      vMark := hviolMarked.2.trans hvmarkSieved }
  simpa [accPrefix, arun_append, selected, sieved, marked] using hall

theorem accPrefix_live_frame (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hR : c.markSteps ≤ st.regs rR) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M) :
    ∀ j, j ≠ c.sink → (arun idx st (accPrefix c)).arr j = st.arr j := by
  let selected := arun idx st c.selectors
  let sieved := arun idx selected c.sieveBody
  have hsel := selectors_acc_run c idx st hidxM hsieveM hsieve hmarkM hR
  dsimp only at hsel
  have hzeroSelected : selected.regs rZero = 0 := by
    rw [show selected.regs rZero = st.regs rZero from
      ArrayRegFrame.arun_frame idx rZero c.selectors (by rfl) st,
      hzero]
  have hsieveLive := sieve_inactive_live_frame c idx selected hsel.1
    hzeroSelected hsinkM
  have hgate42 : sieved.regs 42 = 0 := by
    rw [show sieved.regs 42 = selected.regs 42 from
      ArrayRegFrame.arun_frame idx 42 c.sieveBody (by rfl) selected,
      hsel.2.2.1]
  have hmarkLive := mark_inactive_live_frame c idx sieved hgate42 hsinkM
  intro j hj
  rw [accPrefix, arun_append, arun_append]
  exact (hmarkLive j hj).trans ((hsieveLive j hj).trans (congrFun hsel.2.2.2.2 j))

theorem body_acc_decomp (c : Cfg) :
    c.body = accPrefix c ++ c.accBody ++ c.tailBody := by
  simp [Cfg.body, accPrefix, Cfg.accBody, List.append_assoc]

theorem body_acc_sink_clear_of_parts (c : Cfg) (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkM : c.markSteps < M)
    (hR : c.markSteps ≤ st.regs rR) (hzero : st.regs rZero = 0)
    (hsinkM : c.sink < M)
    (hacc :
      let prefixed := arun idx st (accPrefix c)
      SinkClearSpec c prefixed (arun idx prefixed c.accBody)) :
    SinkClearSpec c st (arun idx st c.body) := by
  let prefixed := arun idx st (accPrefix c)
  let accumulated := arun idx prefixed c.accBody
  let out := arun idx accumulated c.tailBody
  have hpref := accPrefix_live_frame c idx st hidxM hsieveM hsieve hmarkM
    hR hzero hsinkM
  have houtArr : out.arr = accumulated.arr := by
    exact arun_store_free_arr idx c.tailBody accumulated (by rfl)
  have hacc' : SinkClearSpec c prefixed accumulated := by
    simpa [prefixed, accumulated] using hacc
  have hall : SinkClearSpec c st out :=
    { sink_zero := by rw [houtArr]; exact hacc'.sink_zero
      live := by
        intro j hj
        rw [houtArr]
        exact (hacc'.live j hj).trans (hpref j hj) }
  rw [body_acc_decomp, arun_append, arun_append]
  simpa [prefixed, accumulated, out] using hall

structure OuterMiddleSpec (c : Cfg) (k : Nat) (p : Bracket)
    (before after : AState) : Prop where
  arr : SinkClearSpec c before after
  low : after.regs rSl = (step c.wScale k p).lo
  high : after.regs rSh = (step c.wScale k p).hi
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi)
  round : after.regs rKr = before.regs rKr + 1
  cell : after.regs rC = before.regs rC

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem body_middle_live_run (c : Cfg) (idx : Nat) (st : AState)
    (k : Nat) (p : Bracket)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR)
    (hkr0 : st.regs rKr ≠ 0) (hkrLast : st.regs rKr ≠ c.bsSteps)
    (hzero : st.regs rZero = 0) (hbsM : c.bsSteps < M)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hkey : st.regs rK = k)
    (hk : 0 < k) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + k < M)
    (hlow : st.regs rSl = p.lo) (hhigh : st.regs rSh = p.hi)
    (hlohi : p.lo ≤ p.hi) (hhiM : p.hi < M)
    (hfit : RoundFit c k p)
    (haLe : c.wScale / midpoint p ≤ 2147483648)
    (hkrFit : st.regs rKr + 1 < M) :
    OuterMiddleSpec c k p st (arun idx st c.body) := by
  let prefixed := arun idx st (accPrefix c)
  let accumulated := arun idx prefixed c.accBody
  let out := arun idx accumulated c.tailBody
  have hp := accPrefix_latches c idx st hidxM hsieveM hsieve hmarkM
    hmarkPos hR hword harrword
  have hwPref := arun_word idx (accPrefix c) st hword harrword
  have hh := accHead_middle_run c idx prefixed
    (by rw [hp.round]; exact hkr0)
    (by rw [hp.round]; exact hkrLast) hp.gate
    (by rw [hp.zero, hzero]) hbsM hsinkM hwPref.1 hwPref.2
    (by rw [hp.key, hkey]; exact hk) hWM
    (by rw [hp.dPos, hp.dNeg]; exact hsum)
    (by rw [hp.key, hkey]; exact hceilFit)
  have hfitPref : RoundFit c (prefixed.regs rK)
      ⟨prefixed.regs rSl, prefixed.regs rSh⟩ := by
    rw [hp.key, hp.low, hp.high, hkey, hlow, hhigh]
    exact hfit
  have hquotPref : c.wScale /
      midpoint ⟨prefixed.regs rSl, prefixed.regs rSh⟩ ≤ 2147483648 := by
    rw [hp.low, hp.high, hlow, hhigh]
    exact haLe
  have hm := accBody_middle_live_of_head c idx prefixed hh
    (by rw [hp.low, hp.high, hlow, hhigh]; exact hlohi)
    (by rw [hp.high, hhigh]; exact hhiM)
    hfitPref hquotPref
    (by rw [hp.round, hp.gate]; exact hkrFit) hwPref.1 hwPref.2
  have hprefLive := accPrefix_live_frame c idx st hidxM hsieveM hsieve
    hmarkM hR hzero hsinkM
  have prefFrame (j : Nat)
      (hw : ArrayRegFrame.writes j (accPrefix c) = false) :
      prefixed.regs j = st.regs j := by
    exact ArrayRegFrame.arun_frame idx j (accPrefix c) hw st
  have tailFrame (j : Nat)
      (hw : ArrayRegFrame.writes j c.tailBody = false) :
      out.regs j = accumulated.regs j := by
    exact ArrayRegFrame.arun_frame idx j c.tailBody hw accumulated
  have tailArr : out.arr = accumulated.arr :=
    arun_store_free_arr idx c.tailBody accumulated (by rfl)
  have hall : OuterMiddleSpec c k p st out :=
    { arr :=
        { sink_zero := by rw [tailArr]; exact hm.arr.sink_zero
          live := by
            intro j hj
            rw [tailArr]
            exact (hm.arr.live j hj).trans (hprefLive j hj) }
      low := by rw [tailFrame rSl (by rfl), hm.low, hp.key, hp.low, hp.high,
        hkey, hlow, hhigh]
      high := by rw [tailFrame rSh (by rfl), hm.high, hp.key, hp.low, hp.high,
        hkey, hlow, hhigh]
      uPos := by rw [tailFrame rUpLo (by rfl), tailFrame rUpHi (by rfl),
        hm.uPos, prefFrame rUpLo (by rfl), prefFrame rUpHi (by rfl)]
      uNeg := by rw [tailFrame rUnLo (by rfl), tailFrame rUnHi (by rfl),
        hm.uNeg, prefFrame rUnLo (by rfl), prefFrame rUnHi (by rfl)]
      viol := by rw [tailFrame rViol (by rfl), hm.viol, hp.viol]
      vDiv := by rw [tailFrame rVDiv (by rfl), hm.vDiv,
        prefFrame rVDiv (by rfl)]
      vBisect := by rw [tailFrame rVBisect (by rfl), hm.vBisect,
        prefFrame rVBisect (by rfl)]
      v := by rw [tailFrame rVLo (by rfl), tailFrame rVHi (by rfl), hm.v,
        prefFrame rVLo (by rfl), prefFrame rVHi (by rfl)]
      round := by rw [tailFrame rKr (by rfl), hm.round, hp.round, hp.gate]
      cell := by rw [tailFrame rC (by rfl), hm.cell, hp.cell] }
  rw [body_acc_decomp, arun_append, arun_append]
  simpa [prefixed, accumulated, out] using hall

structure OuterFinalSpec (c : Cfg) (s d : Nat)
    (before after : AState) : Prop where
  arr : SinkClearSpec c before after
  low : after.regs rSl = s
  high : after.regs rSh = s
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) =
    AddWide.wval (before.regs rUpLo, before.regs rUpHi)
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) =
    AddWide.wval (before.regs rUnLo, before.regs rUnHi)
  viol : after.regs rViol = before.regs rViol
  vDiv : after.regs rVDiv = before.regs rVDiv
  vBisect : after.regs rVBisect = before.regs rVBisect
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) =
    AddWide.wval (before.regs rVLo, before.regs rVHi) + d * s
  round : after.regs rKr = 0
  cell : after.regs rC = before.regs rC + 1

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem body_final_live_run (c : Cfg) (idx : Nat) (st : AState)
    (s : Nat)
    (hidxM : idx < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ idx) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hR : c.markSteps ≤ st.regs rR)
    (hkrLast : st.regs rKr = c.bsSteps) (hbsPos : 0 < c.bsSteps)
    (hzero : st.regs rZero = 0) (hbsM : c.bsSteps < M)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hk : 0 < st.regs rK)
    (hWM : c.wScale < M) (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M)
    (hlohi : st.regs rSl ≤ st.regs rSh) (hhiM : st.regs rSh < M)
    (hfit : RoundFit c (st.regs rK) ⟨st.regs rSl, st.regs rSh⟩)
    (haLe : c.wScale / midpoint ⟨st.regs rSl, st.regs rSh⟩ ≤
      2147483648)
    (hstep : step c.wScale (st.regs rK)
      ⟨st.regs rSl, st.regs rSh⟩ = ⟨s, s⟩)
    (hcFit : st.regs rC + 1 < M)
    (haccFit : AddWide.wval (st.regs rVLo, st.regs rVHi) +
      (st.regs rDp + st.regs rDn) * s < AddWide.B128) :
    OuterFinalSpec c s (st.regs rDp + st.regs rDn) st
      (arun idx st c.body) := by
  let prefixed := arun idx st (accPrefix c)
  let accumulated := arun idx prefixed c.accBody
  let out := arun idx accumulated c.tailBody
  have hp := accPrefix_latches c idx st hidxM hsieveM hsieve hmarkM
    hmarkPos hR hword harrword
  have hwPref := arun_word idx (accPrefix c) st hword harrword
  have hh := accHead_last_run c idx prefixed
    (by rw [hp.round]; exact hkrLast) hbsPos hp.gate
    (by rw [hp.zero]; exact hzero) hbsM hsinkM hwPref.1 hwPref.2
    (by rw [hp.key]; exact hk) hWM
    (by rw [hp.dPos, hp.dNeg]; exact hsum)
    (by rw [hp.key]; exact hceilFit)
  have hfitPref : RoundFit c (prefixed.regs rK)
      ⟨prefixed.regs rSl, prefixed.regs rSh⟩ := by
    rw [hp.key, hp.low, hp.high]
    exact hfit
  have hquotPref : c.wScale /
      midpoint ⟨prefixed.regs rSl, prefixed.regs rSh⟩ ≤ 2147483648 := by
    rw [hp.low, hp.high]
    exact haLe
  have hstepPref : step c.wScale (prefixed.regs rK)
      ⟨prefixed.regs rSl, prefixed.regs rSh⟩ = ⟨s, s⟩ := by
    rw [hp.key, hp.low, hp.high]
    exact hstep
  have haccPref : AddWide.wval (prefixed.regs rVLo, prefixed.regs rVHi) +
      (prefixed.regs rDp + prefixed.regs rDn) * s < AddWide.B128 := by
    rw [hp.dPos, hp.dNeg]
    rw [show prefixed.regs rVLo = st.regs rVLo from
      ArrayRegFrame.arun_frame idx rVLo (accPrefix c) (by rfl) st]
    rw [show prefixed.regs rVHi = st.regs rVHi from
      ArrayRegFrame.arun_frame idx rVHi (accPrefix c) (by rfl) st]
    exact haccFit
  have hf := accBody_final_live_of_head c idx prefixed s hh
    (by rw [hp.low, hp.high]; exact hlohi)
    (by rw [hp.high]; exact hhiM) hfitPref hquotPref hstepPref
    (by rw [hp.cell]; exact hcFit) haccPref hwPref.1 hwPref.2
  have hprefLive := accPrefix_live_frame c idx st hidxM hsieveM hsieve
    hmarkM hR hzero hsinkM
  have prefFrame (j : Nat)
      (hw : ArrayRegFrame.writes j (accPrefix c) = false) :
      prefixed.regs j = st.regs j := by
    exact ArrayRegFrame.arun_frame idx j (accPrefix c) hw st
  have tailFrame (j : Nat)
      (hw : ArrayRegFrame.writes j c.tailBody = false) :
      out.regs j = accumulated.regs j := by
    exact ArrayRegFrame.arun_frame idx j c.tailBody hw accumulated
  have tailArr : out.arr = accumulated.arr :=
    arun_store_free_arr idx c.tailBody accumulated (by rfl)
  have hall : OuterFinalSpec c s (st.regs rDp + st.regs rDn) st out :=
    { arr :=
        { sink_zero := by rw [tailArr]; exact hf.arr.sink_zero
          live := by
            intro j hj
            rw [tailArr]
            exact (hf.arr.live j hj).trans (hprefLive j hj) }
      low := by rw [tailFrame rSl (by rfl), hf.low]
      high := by rw [tailFrame rSh (by rfl), hf.high]
      uPos := by rw [tailFrame rUpLo (by rfl), tailFrame rUpHi (by rfl),
        hf.uPos, prefFrame rUpLo (by rfl), prefFrame rUpHi (by rfl)]
      uNeg := by rw [tailFrame rUnLo (by rfl), tailFrame rUnHi (by rfl),
        hf.uNeg, prefFrame rUnLo (by rfl), prefFrame rUnHi (by rfl)]
      viol := by rw [tailFrame rViol (by rfl), hf.viol, hp.viol]
      vDiv := by rw [tailFrame rVDiv (by rfl), hf.vDiv,
        prefFrame rVDiv (by rfl)]
      vBisect := by rw [tailFrame rVBisect (by rfl), hf.vBisect,
        prefFrame rVBisect (by rfl)]
      v := by rw [tailFrame rVLo (by rfl), tailFrame rVHi (by rfl), hf.v,
        prefFrame rVLo (by rfl), prefFrame rVHi (by rfl), hp.dPos, hp.dNeg]
      round := by rw [tailFrame rKr (by rfl), hf.round]
      cell := by rw [tailFrame rC (by rfl), hf.cell, hp.cell] }
  rw [body_acc_decomp, arun_append, arun_append]
  simpa [prefixed, accumulated, out] using hall

def tailS (c : Cfg) : List Instr :=
  [ .binop 210 .add (.reg rR) (.reg 41)
  , .binop 211 .eq (.reg 210) (.lit c.period)
  , .binop 212 .sub (.lit 1) (.reg 211)
  , .binop rR .mul (.reg 210) (.reg 212)
  , .binop 213 .mul (.reg 211) (.lit c.segLen)
  , .binop rW .add (.reg rW) (.reg 213) ]

theorem tail_lift (c : Cfg) : c.tailBody = lift (tailS c) := rfl

theorem tail_continue_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 41 = 1) (hnext : st.regs rR + 1 < c.period)
    (hnextM : st.regs rR + 1 < M) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hword : ∀ j, st.regs j < M) :
    let out := arun idx st c.tailBody
    out.regs rR = st.regs rR + 1 ∧ out.regs rW = st.regs rW ∧
      out.arr = st.arr := by
  rw [tail_lift, arun_lift]
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hperiodM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have hwMod' : st.regs 3 % M = st.regs 3 := by
    exact Nat.mod_eq_of_lt (by simpa [rW] using hword rW)
  have hne : st.regs rR + 1 ≠ c.period := by omega
  have hnextM' : st.regs 2 + 1 < M := by simpa [rR] using hnextM
  have hnextMod' : (st.regs 2 + 1) % M = st.regs 2 + 1 := by
    exact Nat.mod_eq_of_lt hnextM'
  have hne' : st.regs 2 + 1 ≠ c.period := by simpa [rR] using hne
  simp [tailS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rR, rW, hgate, hnextMod', hperiodMod, hsegMod, hwMod', hne']

theorem tail_wrap_run (c : Cfg) (idx : Nat) (st : AState)
    (hgate : st.regs 41 = 1) (hnext : st.regs rR + 1 = c.period)
    (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hWnext : st.regs rW + c.segLen < M) :
    let out := arun idx st c.tailBody
    out.regs rR = 0 ∧ out.regs rW = st.regs rW + c.segLen ∧
      out.arr = st.arr := by
  rw [tail_lift, arun_lift]
  have hperiodMod : c.period % M = c.period := Nat.mod_eq_of_lt hperiodM
  have hsegMod : c.segLen % M = c.segLen := Nat.mod_eq_of_lt hsegM
  have hnext' : st.regs 2 + 1 = c.period := by simpa [rR] using hnext
  have hzero : (1 + (M - 1)) % M = 0 := by decide
  have hWnext' : st.regs 3 + c.segLen < M := by simpa [rW] using hWnext
  have hWmod' : (st.regs 3 + c.segLen) % M = st.regs 3 + c.segLen :=
    Nat.mod_eq_of_lt hWnext'
  simp [tailS, srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    rR, rW, hgate, hperiodMod, hsegMod, hnext', hzero, hWmod']

end LeanCompCert.Ports.CDEMAbelOuter

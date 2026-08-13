import LeanCompCert.Ports.MobiusExtremaTrial
import LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest
import LeanCompCert.Verified.Package

/-!
# Compiled trial-division certificate for the Platt prefix through 100

The historical segmented campaign has a handful of irregular bootstrap rows
before its uniform root schedules begin at candidate `101`.  Instead of
replaying those implementation-specific rows in the kernel, this file checks
the same mathematical prefix with the fully denoted scalar trial producer.

There are two independently observable outputs from the identical 900-round
body: a signed-word safety check and the exact accumulator word handed to the
first regular segmented row.  The paper bound itself has a decreasing
candidate-dependent threshold and is therefore checked by the historical
window computations, not by pretending that its endpoint threshold applies
to every earlier candidate.  Both observations here are ordinary LeanCompCert
computations; the named atoms below contain only their physical CompCert run
results.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlatt211Prefix100Certificate

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.MertensCDEM
open LeanCompCert.Ports.MobiusExtremaTrial
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest

/-- Trial every candidate in `[1, 100]` by divisors `2, ..., 10`.
The comparison fields belong to the shared CDEM producer and are deliberately
inert for this extrema-only certificate. -/
def prefixCfg : Cfg where
  lo := 1
  len := 100
  rounds := 9
  bias := 101
  m0 := 101
  lower := 101
  den := 1
  slack := 0
  cap := 101
  anchorX := 101
  anchorM := 101

theorem prefixCfg_admissible : Admissible prefixCfg := by
  constructor <;> decide

theorem prefixCfg_cover :
    ∀ n, n < prefixCfg.len →
      prefixCfg.lo + n < (prefixCfg.rounds + 2) ^ 2 := by
  intro n hn
  simp only [prefixCfg] at hn ⊢
  omega

/-- The unbiased fixed-point state used at candidate one. -/
def prefixExt : MobiusExtremaScalar.Ext :=
  ⟨ArraySegSieve.tBias, ArraySegSieve.tBias, ArraySegSieve.tBias⟩

theorem prefixExt_word : MobiusExtremaScalar.ExtWord prefixExt := by
  constructor <;> decide

def prefixWordSafetyProgram : Program :=
  fullProgram prefixCfg (ArraySegSieve.tBias - 1) prefixExt

def prefixTProgram : Program := tProgram prefixCfg prefixExt

theorem prefixWordSafetyProgram_wf : prefixWordSafetyProgram.WF := by
  decide

theorem prefixTProgram_wf : prefixTProgram.WF := by
  decide

def prefixWordSafetyComputation : Computation :=
  prefixWordSafetyProgram.toComputation
    "platt211-prefix-100-word-safety" prefixWordSafetyProgram_wf

def prefixTComputation : Computation :=
  prefixTProgram.toComputation
    "platt211-prefix-100-accumulator" prefixTProgram_wf

/-- CompCert returned zero signed-word safety failures for candidates 1--100. -/
axiom platt211Prefix100WordSafety_compcert_run :
  prefixWordSafetyComputation.Returns ((0 : Nat) : Int)

/-- CompCert returned the exact accumulator word consumed by manifest row 75. -/
axiom platt211Prefix100T_compcert_run :
  prefixTComputation.Returns ((9366940894763051949 : Nat) : Int)

theorem prefixWordSafetyProgram_denote :
    prefixWordSafetyProgram.denote = some 0 := by
  exact (toComputation_returns prefixWordSafetyProgram
    "platt211-prefix-100-word-safety" prefixWordSafetyProgram_wf 0).mp
      platt211Prefix100WordSafety_compcert_run

theorem prefixTProgram_denote :
    prefixTProgram.denote = some 9366940894763051949 := by
  exact (toComputation_returns prefixTProgram
    "platt211-prefix-100-accumulator" prefixTProgram_wf
      9366940894763051949).mp platt211Prefix100T_compcert_run

/-! ## Per-prefix observations for the paper-varying threshold -/

/-- One externally observed accumulator prefix.  Keeping the candidate and
word together makes the physical batch receipt independent of any Lean
evaluation of Möbius values. -/
structure PrefixObservation where
  n : Nat
  t : Nat
  deriving Repr, DecidableEq

/-- Exact words returned by the 100 independently compiled prefix programs.
Candidate one is retained because it is the base case for the signed-word
bridge, although the paper inequality at one is proved algebraically. -/
def prefixObservations : List PrefixObservation :=
  [ ⟨1, 13835058055282163712⟩
  , ⟨2, 11529215046068469760⟩
  , ⟨3, 9991986373259340459⟩
  , ⟨4, 9991986373259340459⟩
  , ⟨5, 9069649169573862878⟩
  , ⟨6, 9838263505978427529⟩
  , ⟨7, 9179451217631657828⟩
  , ⟨8, 9179451217631657828⟩
  , ⟨9, 9179451217631657828⟩
  , ⟨10, 9640619819474396618⟩
  , ⟨11, 9221375635980997718⟩
  , ⟨12, 9221375635980997718⟩
  , ⟨13, 8866630557640429418⟩
  , ⟨14, 9196036701813814268⟩
  , ⟨15, 9503482436375640128⟩
  , ⟨16, 9503482436375640128⟩
  , ⟨17, 9232206788232852604⟩
  , ⟨18, 9232206788232852604⟩
  , ⟨19, 8989486471473516399⟩
  , ⟨20, 8989486471473516399⟩
  , ⟨21, 9209090567589106299⟩
  , ⟨22, 9418712659335805749⟩
  , ⟨23, 9218204571578093231⟩
  , ⟨24, 9218204571578093231⟩
  , ⟨25, 9218204571578093231⟩
  , ⟨26, 9395577110748377381⟩
  , ⟨27, 9395577110748377381⟩
  , ⟨28, 9395577110748377381⟩
  , ⟨29, 9236553454940536419⟩
  , ⟨30, 9082830587659623489⟩
  , ⟨31, 8934066522549062589⟩
  , ⟨32, 8934066522549062589⟩
  , ⟨33, 9073814583713528889⟩
  , ⟨34, 9209452407784922651⟩
  , ⟨35, 9341214865454276591⟩
  , ⟨36, 9341214865454276591⟩
  , ⟨37, 9216574702794076918⟩
  , ⟨38, 9337934861173745021⟩
  , ⟨39, 9456183220620601121⟩
  , ⟨40, 9456183220620601121⟩
  , ⟨41, 9343703073829689221⟩
  , ⟨42, 9233901025771894271⟩
  , ⟨43, 9126652513715443390⟩
  , ⟨44, 9126652513715443390⟩
  , ⟨45, 9126652513715443390⟩
  , ⟨46, 9226906557594299649⟩
  , ⟨47, 9128785578478823311⟩
  , ⟨48, 9128785578478823311⟩
  , ⟨49, 9128785578478823311⟩
  , ⟨50, 9128785578478823311⟩
  , ⟨51, 9219210794526419152⟩
  , ⟨52, 9219210794526419152⟩
  , ⟨53, 9132197850782506173⟩
  , ⟨54, 9132197850782506173⟩
  , ⟨55, 9216046687481185953⟩
  , ⟨56, 9216046687481185953⟩
  , ⟨57, 9296953459734298021⟩
  , ⟨58, 9376465287638218502⟩
  , ⟨59, 9298301117834364470⟩
  , ⟨60, 9298301117834364470⟩
  , ⟨61, 9222699707696210570⟩
  , ⟨62, 9297081740251491020⟩
  , ⟨63, 9297081740251491020⟩
  , ⟨64, 9297081740251491020⟩
  , ⟨65, 9368030755919604680⟩
  , ⟨66, 9298156725337371530⟩
  , ⟨67, 9229325590733977681⟩
  , ⟨68, 9229325590733977681⟩
  , ⟨69, 9296161619986548520⟩
  , ⟨70, 9230280391151871550⟩
  , ⟨71, 9165327066948668903⟩
  , ⟨72, 9165327066948668903⟩
  , ⟨73, 9102153285874321123⟩
  , ⟨74, 9164473367204420960⟩
  , ⟨75, 9164473367204420960⟩
  , ⟨76, 9164473367204420960⟩
  , ⟨77, 9224365393417763660⟩
  , ⟨78, 9165241213694335610⟩
  , ⟨79, 9106865441309178801⟩
  , ⟨80, 9106865441309178801⟩
  , ⟨81, 9106865441309178801⟩
  , ⟨82, 9163105514704634751⟩
  , ⟨83, 9107543032554907186⟩
  , ⟨84, 9107543032554907186⟩
  , ⟨85, 9161798162183464691⟩
  , ⟨86, 9215422418211690132⟩
  , ⟨87, 9268430303480970453⟩
  , ⟨88, 9268430303480970453⟩
  , ⟨89, 9216613606644707668⟩
  , ⟨90, 9216613606644707668⟩
  , ⟨91, 9267291474979074568⟩
  , ⟨92, 9267291474979074568⟩
  , ⟨93, 9316879496682594868⟩
  , ⟨94, 9365939986240333037⟩
  , ⟨95, 9414484049592200278⟩
  , ⟨96, 9414484049592200278⟩
  , ⟨97, 9366940894763051949⟩
  , ⟨98, 9366940894763051949⟩
  , ⟨99, 9366940894763051949⟩
  , ⟨100, 9366940894763051949⟩ ]

/-- Historical window containing a prefix candidate.  Windows are singleton
through 49, paired through 99, and singleton again at 100. -/
def prefixWindowIndex (n : Nat) : Nat :=
  if n ≤ 49 then n - 1 else if n = 100 then 74 else 49 + (n - 50) / 2

/-- Cheap literal checks attached to every externally observed word.  These
do not calculate Möbius values: they only locate the word in the already
threshold-certified manifest and check ordinary integer comparisons. -/
def prefixObservationScalar (obs : PrefixObservation) : Bool :=
  match rows[prefixWindowIndex obs.n]? with
  | none => false
  | some row => decide (
      1 ≤ obs.n ∧ obs.n ≤ 100 ∧
      row.idx = prefixWindowIndex obs.n ∧
      row.lo ≤ obs.n ∧ obs.n ≤ row.hi ∧ row.hi ≤ 100 ∧
      (obs.n = 1 ∨
        (ArraySegSieve.mobScale ≤ obs.t ∧
          obs.t < 3 * ArraySegSieve.mobScale ∧
          ArraySegSieve.tBias - row.strictThreshold ≤ obs.t ∧
          obs.t ≤ ArraySegSieve.tBias + row.strictThreshold)))

def prefixObservationScalarsOK : Bool :=
  prefixObservations.all prefixObservationScalar

set_option maxRecDepth 10000 in
theorem prefixObservationScalars_ok : prefixObservationScalarsOK = true := by
  decide

theorem prefixObservation_scalar (obs : PrefixObservation)
    (hobs : obs ∈ prefixObservations) :
    ∃ row, rows[prefixWindowIndex obs.n]? = some row ∧
      1 ≤ obs.n ∧ obs.n ≤ 100 ∧
      row.idx = prefixWindowIndex obs.n ∧
      row.lo ≤ obs.n ∧ obs.n ≤ row.hi ∧ row.hi ≤ 100 ∧
      (obs.n = 1 ∨
        (ArraySegSieve.mobScale ≤ obs.t ∧
          obs.t < 3 * ArraySegSieve.mobScale ∧
          ArraySegSieve.tBias - row.strictThreshold ≤ obs.t ∧
          obs.t ≤ ArraySegSieve.tBias + row.strictThreshold)) := by
  have h := (List.all_eq_true.mp prefixObservationScalars_ok) obs hobs
  unfold prefixObservationScalar at h
  split at h
  · contradiction
  · rename_i row heq
    exact ⟨row, heq, of_decide_eq_true h⟩

/-- Ordered coverage of every candidate prefix. -/
def prefixObservationCoverageOK : Bool :=
  (List.range 100).all fun k =>
    match prefixObservations[k]? with
    | none => false
    | some obs => decide (obs.n = k + 1)

theorem prefixObservationCoverage_ok : prefixObservationCoverageOK = true := by
  decide

theorem prefixObservation_exists (n : Nat) (hn : 1 ≤ n) (hn100 : n ≤ 100) :
    ∃ obs, obs ∈ prefixObservations ∧ obs.n = n := by
  have hk : n - 1 ∈ List.range 100 := List.mem_range.mpr (by omega)
  have h := (List.all_eq_true.mp prefixObservationCoverage_ok) (n - 1) hk
  unfold prefixObservationCoverageOK at h
  split at h
  · contradiction
  · rename_i obs heq
    refine ⟨obs, List.mem_of_getElem? heq, ?_⟩
    have hnEq := of_decide_eq_true h
    omega

/-- Reuse the proved trial configuration while stopping after one advertised
prefix. -/
def prefixCfgAt (n : Nat) : Cfg := { prefixCfg with len := n }

theorem prefixCfgAt_wf (n : Nat) :
    (tProgram (prefixCfgAt n) prefixExt).WF := by
  simp +decide [Program.WF, tProgram, prefixCfgAt, prefixCfg, fullBody,
    MertensCDEM.body, MertensCDEM.bodyA, MertensCDEM.bodyB,
    MertensCDEM.bodyC, MertensCDEM.bodyC1, MertensCDEM.bodyC2,
    MertensCDEM.bodyC2a, MertensCDEM.bodyC2b, MertensCDEM.initBlock,
    MobiusResidueTrial.signalBlock, MobiusExtremaScalar.residue,
    MobiusResidueScalar.scalarOf, ArraySegSieve.mobiusOverNResidue,
    extremaInit, Instr.WF, Operand.WF]

def prefixObservationComputation (row : PrefixObservation) : Computation :=
  (tProgram (prefixCfgAt row.n) prefixExt).toComputation
    s!"platt211-prefix-{row.n}-accumulator" (prefixCfgAt_wf row.n)

/-- Physical CompCert observations for every prefix.  The batch emitter
compiles the exact `prefixObservationComputation` attached to each row and
requires the returned word to equal the retained literal. -/
axiom platt211PrefixObservations_compcert_run
    (row : PrefixObservation) (hrow : row ∈ prefixObservations) :
    (prefixObservationComputation row).Returns (row.t : Int)

theorem prefixObservationProgram_denote
    (row : PrefixObservation) (hrow : row ∈ prefixObservations) :
    (tProgram (prefixCfgAt row.n) prefixExt).denote = some row.t := by
  exact (toComputation_returns (tProgram (prefixCfgAt row.n) prefixExt)
    s!"platt211-prefix-{row.n}-accumulator" (prefixCfgAt_wf row.n)
      row.t).mp (platt211PrefixObservations_compcert_run row hrow)

#print axioms prefixWordSafetyProgram_denote
#print axioms prefixTProgram_denote
#print axioms prefixObservationProgram_denote

end LeanCompCert.Ports.ArraySegMobiusPlatt211Prefix100Certificate

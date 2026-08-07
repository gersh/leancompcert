import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk336

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487471375597407, 362487487167550588⟩, ⟨(-97530544775192262), (-97171921693839172)⟩, true⟩

def state01 : KState := ⟨⟨362454704402775898, 362454720204398001⟩, ⟨1003711747500176214, 1004070695508469014⟩, true⟩

def words00 : List Nat := [371284596204373862, 371284596205460850, 371284596142748143, 371284596019343036, 371284595895547862, 371284595744912294, 371284595151834953, 371284594923004897, 371284594693814847, 371284594369691321]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362517096940197019, 362517112751633744⟩, ⟨(-1093670961523836099), (-1093311683595835135)⟩, true⟩

def words01 : List Nat := [371284593481610629, 371284592988185728, 371284592884541234, 371284592885647480, 371284592539269426, 371284592070889670, 371284592017345944, 371284592101134669, 371284593069173534, 371284594037627741]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362506140291819937, 362506156113078525⟩, ⟨(-725393062240013642), (-725033454051130090)⟩, true⟩

def words02 : List Nat := [371284594837014514, 371284594838101903, 371284594963249679, 371284595469038034, 371284596223428214, 371284596322082555, 371284596322901353, 371284596249192032, 371284596984448190, 371284597626739995]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492688739898980, 362492704570952288⟩, ⟨(-272897242262347714), (-272537304626470926)⟩, true⟩

def words03 : List Nat := [371284598857360637, 371284600088361313, 371284601192461878, 371284601259270637, 371284601377976268, 371284601497185545, 371284602499827852, 371284602743506248, 371284602985158995, 371284603227216179]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362495386426542465, 362495402267354433⟩, ⟨(-363456043601807216), (-363095777634815820)⟩, true⟩

def words04 : List Nat := [371284604352558542, 371284605169549470, 371284606535840711, 371284607902486203, 371284609123848406, 371284609168338870, 371284610095956164, 371284611024095039, 371284611901363925, 371284612223146689]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499449234874389, 362499465085598687⟩, ⟨(-500125685524846013), (-499765085959071303)⟩, true⟩

def words05 : List Nat := [371284612545925795, 371284612869035516, 371284613981067358, 371284614708017003, 371284615626347612, 371284616545069563, 371284617457940339, 371284617459029014, 371284617636646722, 371284618079093858]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486464610605921, 362486480471038419⟩, ⟨(-63031610826390678), (-62670684433213464)⟩, true⟩

def words06 : List Nat := [371284619176465470, 371284619177554221, 371284619099064025, 371284618808968093, 371284618518457962, 371284618497744359, 371284618475953549, 371284618854276020, 371284619148696846, 371284619205129085]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507201185750378, 362507217056029147⟩, ⟨(-761346266864823303), (-760985008897422051)⟩, true⟩

def words07 : List Nat := [371284619713244971, 371284620221900094, 371284621464620145, 371284621660221529, 371284621727508649, 371284621795119658, 371284622025845260, 371284622027056161, 371284622488019004, 371284623160096799]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484897163722319, 362484913043822918⟩, ⟨(-10095164050287894), (-9733575232135902)⟩, true⟩

def words08 : List Nat := [371284623814905776, 371284623816002640, 371284624125960229, 371284624569754256, 371284625282306607, 371284625283396360, 371284624821856381, 371284624359083105, 371284624126723494, 371284624136541088]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362469955851172709, 362469971741099921⟩, ⟨493371946386427275, 493733866311362997⟩, true⟩

def words09 : List Nat := [371284624507931939, 371284624879720584, 371284625080052954, 371284625081145930, 371284624389436838, 371284623819516012, 371284623412912865, 371284623414022979, 371284623031208124, 371284622597667024]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk336

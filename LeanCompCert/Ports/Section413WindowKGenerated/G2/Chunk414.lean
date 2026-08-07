import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk414

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617022779766898, 360617033366783864⟩, ⟨(-1434861284728053916), (-1434565063174666458)⟩, true⟩

def state01 : KState := ⟨⟨360605125615301971, 360605136207613881⟩, ⟨(-942356364521685812), (-942059923731585998)⟩, true⟩

def words00 : List Nat := [360582383963523024, 360582384648444243, 360582384946982101, 360582385245570332, 360582385246051874, 360582385251473895, 360582385829912357, 360582386408430343, 360582386631476279, 360582387181419595]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360632720721724090, 360632731319359166⟩, ⟨(-2085143976719477405), (-2084847315472270297)⟩, true⟩

def words01 : List Nat := [360582388312937299, 360582389444577985, 360582391157686846, 360582392290857820, 360582392841541273, 360582393392238956, 360582394384852358, 360582395788350683, 360582397004060918, 360582398219833026]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360638966129694861, 360638976732686481⟩, ⟨(-2344062764956140515), (-2343765881813415355)⟩, true⟩

def words02 : List Nat := [360582399144098020, 360582399656856158, 360582400440871703, 360582401225013549, 360582401861215832, 360582402822700528, 360582403490589090, 360582404158502097, 360582405023577082, 360582406389662818]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561900856425076, 360561911464725723⟩, ⟨849226592478483375, 849523695601592069⟩, true⟩

def words03 : List Nat := [360582407924271967, 360582409458912584, 360582410538906166, 360582411039416471, 360582411391545700, 360582411743812587, 360582412185335963, 360582412185899085, 360582412048017334, 360582411553905299]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614127312031169, 360614137925647585⟩, ⟨(-1315264409855041631), (-1314967086420341011)⟩, true⟩

def words04 : List Nat := [360582411059679877, 360582410970397268, 360582411652096215, 360582412333872613, 360582412515941791, 360582412834358832, 360582412987786491, 360582413141367587, 360582413749275750, 360582414515201026]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360613738586856644, 360613749205837042⟩, ⟨(-1299098632261428692), (-1298801086463650708)⟩, true⟩

def words05 : List Nat := [360582414905588442, 360582415296018427, 360582416266814323, 360582417696956385, 360582418978848803, 360582420260771169, 360582421176487512, 360582421843090397, 360582422599153668, 360582423355363980]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608106831749576, 360608117456043654⟩, ⟨(-1065792572274179026), (-1065494806144540416)⟩, true⟩

def words06 : List Nat := [360582424098200001, 360582424262331788, 360582424262839927, 360582424014680783, 360582423766441719, 360582423370586016, 360582423739120095, 360582424213737809, 360582424308451934, 360582424928587250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360641081143710229, 360641091773319794⟩, ⟨(-2433445043575961581), (-2433147056986884929)⟩, true⟩

def words07 : List Nat := [360582426006906074, 360582427085344246, 360582428569634358, 360582429646868348, 360582430185643866, 360582430724427694, 360582431204377901, 360582432039474524, 360582433454099524, 360582434868785504]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360607703344397321, 360607713979384320⟩, ⟨(-1048878035196137165), (-1048579825523773487)⟩, true⟩

def words08 : List Nat := [360582435833658504, 360582436812193986, 360582437959023792, 360582439105961255, 360582440105106612, 360582440526284918, 360582440656853516, 360582440787477280, 360582440905090826, 360582441514861321]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553495649003529, 360553506289303782⟩, ⟨1200637101816455792, 1200935531961557096⟩, true⟩

def words09 : List Nat := [360582442703741807, 360582443892677624, 360582444791127310, 360582445111751241, 360582445177381793, 360582445243173099, 360582445505995595, 360582445506559546, 360582445191631770, 360582444494893218]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk414

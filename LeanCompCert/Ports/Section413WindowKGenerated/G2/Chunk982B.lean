import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk982A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk982B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk982A

def state06 : KState := ⟨⟨360557253357054529, 360557317255369032⟩, ⟨2464771117896689476, 2469010667946538574⟩, true⟩

def words05 : List Nat := [360582445936397182, 360582445863142440, 360582445789710508, 360582445663287092, 360582445505744061, 360582445304979429, 360582445103797208, 360582445006416533, 360582444831696456, 360582444577452755]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 98250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 98200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581530124511398, 360581594036294575⟩, ⟨79195786417446594, 83436659965975092⟩, true⟩

def words06 : List Nat := [360582444322886336, 360582444144545211, 360582444028260392, 360582443928104665, 360582443827839795, 360582443639826675, 360582443453599215, 360582443298587410, 360582443143156044, 360582443091550157]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 98260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 98200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564707906130495, 360564771831549409⟩, ⟨1732404632465548780, 1736646846059918780⟩, true⟩

def words07 : List Nat := [360582443084194086, 360582443015129842, 360582442945812761, 360582442853544525, 360582442840060757, 360582442800775079, 360582442761338678, 360582442636905064, 360582442408994593, 360582442230878469]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 98270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 98200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360548143117028114, 360548207055872652⟩, ⟨3360476804498284951, 3364720337632346423⟩, true⟩

def words08 : List Nat := [360582442052238806, 360582441929695322, 360582441726283327, 360582441470284595, 360582441214066260, 360582440891677451, 360582440620496794, 360582440314755292, 360582440008876351, 360582439636375576]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 98280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 98200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582945507313735, 360583009459635061⟩, ⟨(-60460706259439890), (-56215848425965284)⟩, true⟩

def words09 : List Nat := [360582439289251802, 360582439026549895, 360582438763439434, 360582438531438156, 360582438355594457, 360582438092072677, 360582437828272811, 360582437668350521, 360582437577703115, 360582437585000765]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 98290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 98200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 98200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk982B

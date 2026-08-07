import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk982

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565374676146031, 360565438493440246⟩, ⟨1666345947318853151, 1670577538749686827⟩, true⟩

def state01 : KState := ⟨⟨360580720745739971, 360580784576521968⟩, ⟨159281605445923696, 163514521443022892⟩, true⟩

def words00 : List Nat := [360582450312586418, 360582450228148054, 360582450209512296, 360582450188669565, 360582450167716362, 360582450058800213, 360582449846259247, 360582449737793872, 360582449628888472, 360582449524301655]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567864352401113, 360567928196756510⟩, ⟨1422011850264274650, 1426246099374670450⟩, true⟩

def words01 : List Nat := [360582449508622500, 360582449430874551, 360582449377300518, 360582449454990762, 360582449475744835, 360582449496725635, 360582449498030935, 360582449439102547, 360582449276583243, 360582449130368552]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582258022747777, 360582321880544791⟩, ⟨8152768468261905, 12388337878833603⟩, true⟩

def words02 : List Nat := [360582448983682371, 360582448940876248, 360582448825268960, 360582448647269871, 360582448469018081, 360582448265039265, 360582448134756780, 360582448108351618, 360582448081784481, 360582447996170149]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589205012852215, 360589268884119323⟩, ⟨(-674352985597795994), (-670116092952274838)⟩, true⟩

def words03 : List Nat := [360582447996059794, 360582447993889998, 360582448036815651, 360582448038242622, 360582447981794002, 360582447822492723, 360582447662920522, 360582447597751540, 360582447668340735, 360582447739251577]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564868579634526, 360564932464486668⟩, ⟨1716477788033370913, 1720716015340001361⟩, true⟩

def words04 : List Nat := [360582447740537658, 360582447722460002, 360582447600832211, 360582447514789041, 360582447428375538, 360582447270116787, 360582447008429607, 360582446694953815, 360582446381213297, 360582446113497763]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk982

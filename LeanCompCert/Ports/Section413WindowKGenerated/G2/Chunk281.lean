import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk281

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360626878611724777, 360626883334209667⟩, ⟨(-1253211916830531367), (-1253122162663310485)⟩, true⟩

def state01 : KState := ⟨⟨360610957810993982, 360610962537005323⟩, ⟨(-806194606843297938), (-806104753565334456)⟩, true⟩

def words00 : List Nat := [360582290366699221, 360582290367069624, 360582289866112778, 360582290085826102, 360582290086143701, 360582289115329397, 360582288465045418, 360582287135847028, 360582285806672500, 360582286760492025]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564077263578960, 360564081993086697⟩, ⟨512033046534004990, 512122998113007862⟩, true⟩

def words01 : List Nat := [360582289043406766, 360582291326236215, 360582292973901508, 360582293361620513, 360582293424917855, 360582293488315049, 360582294289359474, 360582294695451869, 360582294695789444, 360582294048496122]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360665645099646193, 360665649832651075⟩, ⟨(-2344515996910592746), (-2344425946974696424)⟩, true⟩

def words02 : List Nat := [360582293616632068, 360582294576043636, 360582296796479583, 360582299016828515, 360582300162840625, 360582301659007845, 360582303342357260, 360582305025693348, 360582307281716912, 360582310244759614]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360634536410688095, 360634541147231240⟩, ⟨(-1469335697578437204), (-1469245548093922450)⟩, true⟩

def words03 : List Nat := [360582312574128198, 360582314903373350, 360582317199905903, 360582320149870716, 360582322315314592, 360582324480664167, 360582325973405782, 360582327295685048, 360582329151488780, 360582331007289734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582556698255482, 360582561438290127⟩, ⟨(-6371390522187388), (-6281142768984126)⟩, true⟩

def words04 : List Nat := [360582333802079263, 360582335339257896, 360582336057699697, 360582336776127712, 360582336787338964, 360582337433816786, 360582338048297889, 360582338662801324, 360582338663134275, 360582338315034507]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360675271267241150, 360675276010781726⟩, ⟨(-2616749615376232449), (-2616659268913606737)⟩, true⟩

def words05 : List Nat := [360582339581744847, 360582340848479004, 360582342927926579, 360582345055116663, 360582346110212546, 360582347165262486, 360582348931221383, 360582351571409891, 360582354871584162, 360582358171610049]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613325201290291, 360613329948371543⟩, ⟨(-872305949019015424), (-872215502833123590)⟩, true⟩

def words06 : List Nat := [360582360452476312, 360582361477626078, 360582363759928727, 360582366042177750, 360582367727881097, 360582368158116785, 360582368158447944, 360582367758923379, 360582367381283770, 360582368480804431]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360488015582028719, 360488020332606533⟩, ⟨2658301363344503007, 2658391908046443237⟩, true⟩

def words07 : List Nat := [360582369150554130, 360582369820323791, 360582369858108854, 360582369858480403, 360582368641374638, 360582366375969939, 360582364110618249, 360582362379448496, 360582359801615845, 360582356454254739]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584354677662621, 360584359431754831⟩, ⟨(-56778825809692428), (-56688182054947936)⟩, true⟩

def words08 : List Nat := [360582353107047490, 360582351015953287, 360582350539331087, 360582350929080264, 360582350929422945, 360582350251014005, 360582349176722042, 360582348961412772, 360582348746010927, 360582348570768880]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572218820972467, 360572223578603950⟩, ⟨285338372698204857, 285429116242306559⟩, true⟩

def words09 : List Nat := [360582348571100186, 360582348012000828, 360582347452872204, 360582347402517807, 360582347476989285, 360582347551523263, 360582347551859198, 360582346817156553, 360582345536981197, 360582345178470699]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk281

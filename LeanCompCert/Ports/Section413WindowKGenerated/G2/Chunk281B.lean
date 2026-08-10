import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk281A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk281B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk281A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk281B

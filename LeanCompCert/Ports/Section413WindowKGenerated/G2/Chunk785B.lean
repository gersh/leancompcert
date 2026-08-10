import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk785A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk785B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk785A

def state06 : KState := ⟨⟨360583492411298196, 360583532553092592⟩, ⟨(-102985630285274289), (-100855749484199065)⟩, true⟩

def words05 : List Nat := [360582249768467162, 360582249536664005, 360582249304525886, 360582249234468747, 360582249206048055, 360582249039437031, 360582248872617345, 360582248761029135, 360582248746565837, 360582248764068978]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360583008170714210, 360583048323218233⟩, ⟨(-65059535062716548), (-62928812862282298)⟩, true⟩

def words06 : List Nat := [360582248765097055, 360582248638184727, 360582248486716688, 360582248468100430, 360582248449189248, 360582248352542722, 360582248133778200, 360582247834114434, 360582247534221969, 360582247406685896]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360570090990386267, 360570131153451988⟩, ⟨949962375533449649, 952093927620726721⟩, true⟩

def words07 : List Nat := [360582247579551330, 360582247752632683, 360582247802738289, 360582247803863661, 360582247799872621, 360582247684599418, 360582247614242608, 360582247615365027, 360582247543789405, 360582247390759455]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592897766279022, 360592937939957406⟩, ⟨(-842238350565715651), (-840105964485192401)⟩, true⟩

def words08 : List Nat := [360582247237478979, 360582247322133848, 360582247588989204, 360582247856063164, 360582247988555888, 360582247989678299, 360582248053287260, 360582248147365230, 360582248207728283, 360582248344908543]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588694443955487, 360588734628323380⟩, ⟨(-511897590239703617), (-509764364018126571)⟩, true⟩

def words09 : List Nat := [360582248345913050, 360582248342664737, 360582248496512775, 360582248736072351, 360582248867761431, 360582248999643801, 360582249019635920, 360582249020763925, 360582249075336123, 360582249159130646]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk785B

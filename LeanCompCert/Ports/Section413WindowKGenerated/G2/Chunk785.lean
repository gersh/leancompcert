import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk785

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582515552290712, 360582555630412510⟩, ⟨(-25605574951298759), (-23480694354439723)⟩, true⟩

def state01 : KState := ⟨⟨360568893950987789, 360568934039781890⟩, ⟨1043625419545014146, 1045751137971129048⟩, true⟩

def words00 : List Nat := [360582256518096437, 360582256430831283, 360582256181394405, 360582256020509541, 360582255859348049, 360582255586422383, 360582255259425639, 360582254790134384, 360582254320637980, 360582254013517353]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567244996392121, 360567285095761864⟩, ⟨1173129240741598140, 1175255789514254452⟩, true⟩

def words01 : List Nat := [360582253844766533, 360582253838241449, 360582253831574869, 360582253743890514, 360582253563406945, 360582253304464188, 360582253045186207, 360582252948104502, 360582252883149888, 360582252693692510]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585667542152054, 360585707652103974⟩, ⟨(-273464850384098470), (-271337470646783300)⟩, true⟩

def words02 : List Nat := [360582252503980219, 360582252492191452, 360582252531431346, 360582252570882061, 360582252571927515, 360582252469950908, 360582252425002274, 360582252439251152, 360582252443115965, 360582252488275082]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360571273444743941, 360571313565396369⟩, ⟨856938670884653658, 859066890983199936⟩, true⟩

def words03 : List Nat := [360582252489274498, 360582252453289640, 360582252417110141, 360582252314381617, 360582252292620156, 360582252213119527, 360582252133499053, 360582251957397759, 360582251657144006, 360582251519190401]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360566365932559176, 360566406063765417⟩, ⟨1242409727205769483, 1244538776253539133⟩, true⟩

def words04 : List Nat := [360582251403453582, 360582251404575465, 360582251305406534, 360582251125924108, 360582250946264740, 360582250682518194, 360582250535985311, 360582250374125400, 360582250212147187, 360582249969255596]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk785

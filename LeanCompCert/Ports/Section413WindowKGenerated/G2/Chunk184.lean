import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk184

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360558496274619506, 360558498225038190⟩, ⟨485948984457371304, 485973275550597802⟩, true⟩

def state01 : KState := ⟨⟨360615949938005247, 360615951890638813⟩, ⟨(-571582056635396800), (-571557724777205138)⟩, true⟩

def words00 : List Nat := [360584909893218616, 360584912888346047, 360584914250581356, 360584915612709009, 360584915612927013, 360584914461463503, 360584910379916063, 360584908317825449, 360584906255889496, 360584907529942642]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360585411358915056, 360585413313781007⟩, ⟨(-9139588033968666), (-9115215066539160)⟩, true⟩

def words01 : List Nat := [360584907530152537, 360584906968377949, 360584908788282758, 360584913395376049, 360584916523915385, 360584919652153048, 360584920505948024, 360584920506182706, 360584918459275784, 360584918486406460]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583513218704554, 360583515175780436⟩, ⟨25521742559868183, 25546156245059365⟩, true⟩

def words02 : List Nat := [360584919151571773, 360584919151806531, 360584918056828503, 360584915012694938, 360584911968851056, 360584906808726991, 360584903595102534, 360584903321421578, 360584903047744079, 360584901293862100]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360708534524578404, 360708536483872890⟩, ⟨(-2279578957897006845), (-2279554503311603527)⟩, true⟩

def words03 : List Nat := [360584901218849505, 360584901034646710, 360584903603406369, 360584905555915519, 360584905556131867, 360584904996032659, 360584905917580862, 360584909686796185, 360584916391259419, 360584923095048445]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360633388058123705, 360633390019657478⟩, ⟨(-893885560064112964), (-893861064175691138)⟩, true⟩

def words04 : List Nat := [360584928335401983, 360584930654570993, 360584935908218710, 360584941161365478, 360584943673114665, 360584944925465175, 360584944925676966, 360584943630806739, 360584942336032452, 360584944891253831]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598509261021800, 360598511224772052⟩, ⟨(-250012036436246319), (-249987499642362313)⟩, true⟩

def words05 : List Nat := [360584950448747650, 360584956005687960, 360584960086404227, 360584961249833024, 360584961660568870, 360584962071322123, 360584965411707124, 360584968372606539, 360584969106453786, 360584969840251043]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360706562234595022, 360706564200565310⟩, ⟨(-2244893383869018117), (-2244868806082256021)⟩, true⟩

def words06 : List Nat := [360584973502707898, 360584979206144709, 360584986522549838, 360584993838207320, 360584998649869046, 360585003557130603, 360585010295023776, 360585017032258920, 360585022846446211, 360585029426807406]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590017495706486, 360590019463921592⟩, ⟨(-91751205584027830), (-91726586324321348)⟩, true⟩

def words07 : List Nat := [360585034235756802, 360585039044211265, 360585042092490401, 360585046615139114, 360585050344891188, 360585054074277866, 360585056308860990, 360585056309096482, 360585055903781267, 360585056172631926]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360551748461480498, 360551750431910977⟩, ⟨615641734025660633, 615666394236908073⟩, true⟩

def words08 : List Nat := [360585059363930547, 360585059647312510, 360585059647522368, 360585058046594578, 360585056445801673, 360585054093595902, 360585053679739790, 360585052175218823, 360585050670834889, 360585047694984904]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360629373483145489, 360629375455799881⟩, ⟨(-820157182551176790), (-820132481208709616)⟩, true⟩

def words09 : List Nat := [360585045894448888, 360585043745669288, 360585042367555680, 360585043229829769, 360585043230049078, 360585041521682965, 360585039959266764, 360585041573467189, 360585043970084911, 360585046366496130]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk184

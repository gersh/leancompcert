import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk734A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk734B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk734A

def state06 : KState := ⟨⟨362492205998415335, 362492286386475119⟩, ⟨(-516704757970473647), (-512716737371000999)⟩, true⟩

def words05 : List Nat := [371285307187486476, 371285307122291702, 371285307172753226, 371285307175282372, 371285307102100450, 371285306992998799, 371285306882845900, 371285306840716935, 371285306847352921, 371285306945174688]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473855941674598, 362473936352468044⟩, ⟨831355114715789662, 835344805448373910⟩, true⟩

def words06 : List Nat := [371285307032980820, 371285307035508511, 371285306932397573, 371285306944012240, 371285306962711297, 371285306965235612, 371285306758340603, 371285306550228248, 371285306341128577, 371285306228682123]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469870429544722, 362469950863145294⟩, ⟨1124266746072926294, 1128258112556808756⟩, true⟩

def words07 : List Nat := [371285306105941737, 371285306139067375, 371285306164147460, 371285306166678958, 371285306001876067, 371285305895784618, 371285305864281696, 371285305866806374, 371285305697873740, 371285305491786514]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489149158687439, 362489229614864277⟩, ⟨(-292379744499631000), (-288386718994396274)⟩, true⟩

def words08 : List Nat := [371285305284538295, 371285305252561582, 371285305194066653, 371285305259179646, 371285305275905506, 371285305278476876, 371285305224124187, 371285305276520557, 371285305449520765, 371285305505531238]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481939087446030, 362482019566627110⟩, ⟨237519306709595973, 241514022911705689⟩, true⟩

def words09 : List Nat := [371285305508351546, 371285305511989813, 371285305592043189, 371285305594854699, 371285305624156599, 371285305668811699, 371285305713161204, 371285305715686632, 371285305513249052, 371285305471700739]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk734B

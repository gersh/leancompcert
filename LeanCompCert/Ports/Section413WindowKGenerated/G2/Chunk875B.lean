import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk875A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk875B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk875A

def state06 : KState := ⟨⟨360619264030731240, 360619314318433694⟩, ⟨(-3258125070344526207), (-3255151586126301757)⟩, true⟩

def words05 : List Nat := [360582136162168763, 360582136373695383, 360582136715103167, 360582136926415816, 360582137026090156, 360582137125877294, 360582137355659625, 360582137651381939, 360582138076985874, 360582138502875098]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594413235056323, 360594463534787094⟩, ⟨(-1082190513108177359), (-1079215975633720081)⟩, true⟩

def words06 : List Nat := [360582138839037227, 360582139045008860, 360582139247089055, 360582139449516915, 360582139603058618, 360582139626501712, 360582139627627922, 360582139552876162, 360582139495675824, 360582139637884767]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550237121204543, 360550287432793733⟩, ⟨2786561939516443957, 2789537515492599771⟩, true⟩

def words07 : List Nat := [360582139745830084, 360582139854005506, 360582139896786685, 360582139898047422, 360582139810478696, 360582139667892090, 360582139524955476, 360582139379041213, 360582139102726922, 360582138740346743]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580745667149542, 360580795990642990⟩, ⟨114448151186257277, 117424769796984805⟩, true⟩

def words08 : List Nat := [360582138377692411, 360582138054431842, 360582137829000990, 360582137734029152, 360582137638934208, 360582137433081777, 360582137096729131, 360582136890946709, 360582136684784234, 360582136609090267]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580360043234450, 360580410378748567⟩, ⟨148168749420436517, 151146420981751333⟩, true⟩

def words09 : List Nat := [360582136594928298, 360582136463346369, 360582136331532663, 360582136220468803, 360582136190277727, 360582136127651041, 360582136064898501, 360582135937231547, 360582135812769318, 360582135794513199]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk875B

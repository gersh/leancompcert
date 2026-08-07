import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk875

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360595838342660237, 360595888558830799⟩, ⟨(-1206043021572457516), (-1203075798534351626)⟩, true⟩

def state01 : KState := ⟨⟨360572613813760584, 360572664041915215⟩, ⟨826105565413347441, 829073837117617853⟩, true⟩

def words00 : List Nat := [360582139371149870, 360582139372409645, 360582139373121446, 360582139370738162, 360582139368028905, 360582139249796643, 360582139000998759, 360582138653460818, 360582138305689204, 360582138088734066]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570724115172308, 360570774355195510⟩, ⟨991553479415861600, 994522789795086034⟩, true⟩

def words01 : List Nat := [360582138003618800, 360582138027005826, 360582138028128954, 360582137982643639, 360582137983699358, 360582137920691864, 360582137923232626, 360582137924492505, 360582137861127278, 360582137732592621]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575882772671565, 360575933024599246⟩, ⟨540065950620220371, 543036302938794403⟩, true⟩

def words02 : List Nat := [360582137603792722, 360582137472121034, 360582137497903251, 360582137576722172, 360582137577896407, 360582137546314778, 360582137413776543, 360582137271909525, 360582137129656243, 360582137026689259]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360572075618683287, 360572125882603850⟩, ⟨873257650101065309, 876229052215810003⟩, true⟩

def words03 : List Nat := [360582136956934029, 360582136812566063, 360582136667964661, 360582136507114798, 360582136410417462, 360582136198659409, 360582135986768659, 360582135709704259, 360582135466062116, 360582135353156921]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594246323435247, 360594296599241476⟩, ⟨(-1067649354837408075), (-1064676912193097829)⟩, true⟩

def words04 : List Nat := [360582135255806643, 360582135349653401, 360582135363066447, 360582135376607022, 360582135377661613, 360582135403839315, 360582135580346521, 360582135757091869, 360582135810813336, 360582135951022803]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk875

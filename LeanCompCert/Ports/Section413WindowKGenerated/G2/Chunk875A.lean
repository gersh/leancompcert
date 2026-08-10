import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk875A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk875A

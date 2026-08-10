import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk755A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575539166855027, 360575576126546845⟩, ⟨498594811399428734, 500479540453897614⟩, true⟩

def state01 : KState := ⟨⟨360572423426491739, 360572460396450604⟩, ⟨733834527283382863, 735720031549807309⟩, true⟩

def words00 : List Nat := [360582204907801234, 360582204732674094, 360582204567278013, 360582204572938004, 360582204573838267, 360582204535079015, 360582204421896919, 360582204221074634, 360582204020068260, 360582203742120712]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360548978146784107, 360549015126871718⟩, ⟨2504395682460264694, 2506281951599221794⟩, true⟩

def words01 : List Nat := [360582203660073598, 360582203707263234, 360582203708221653, 360582203667676645, 360582203569454450, 360582203356481625, 360582203143181067, 360582202912755375, 360582202561391421, 360582202123052852]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590828531580446, 360590865521838284⟩, ⟨(-656394170741780346), (-654507133498420156)⟩, true⟩

def words02 : List Nat := [360582201684482027, 360582201421345418, 360582201269508172, 360582201113837124, 360582200958090173, 360582200656866778, 360582200330255332, 360582200179058490, 360582200027539354, 360582200111165866]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588790214576068, 360588827215068774⟩, ⟨(-502432405466930636), (-500544595132631088)⟩, true⟩

def words03 : List Nat := [360582200112127083, 360582200104798234, 360582200263911199, 360582200519676405, 360582200730866665, 360582200942226675, 360582200992330272, 360582200993406209, 360582200994684370, 360582201083628462]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588804908855460, 360588841919484826⟩, ⟨(-503552003172375729), (-501663427065084145)⟩, true⟩

def words04 : List Nat := [360582201347236179, 360582201478140771, 360582201491538458, 360582201505069632, 360582201505971049, 360582201462496365, 360582201593163624, 360582201724043025, 360582201767117974, 360582201856122792]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk755A

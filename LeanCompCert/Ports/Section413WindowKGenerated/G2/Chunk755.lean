import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk755

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

def state06 : KState := ⟨⟨360604068117750006, 360604105138549016⟩, ⟨(-1656826769663824297), (-1654937425190293825)⟩, true⟩

def words05 : List Nat := [360582201894696488, 360582201933569343, 360582202147097524, 360582202261169127, 360582202262172584, 360582202212764551, 360582202287618269, 360582202551490537, 360582202842236659, 360582203133213059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360568213057517272, 360568250088562556⟩, ⟨1052434517246895771, 1054324635979655443⟩, true⟩

def words06 : List Nat := [360582203328868771, 360582203349722563, 360582203363046720, 360582203376695051, 360582203377614186, 360582203227807555, 360582202902983093, 360582202490637119, 360582202078100251, 360582201717991955]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566310829669028, 360566347870855351⟩, ⟨1196244740046860998, 1198135625188148550⟩, true⟩

def words07 : List Nat := [360582201534246142, 360582201525620394, 360582201516868900, 360582201417110048, 360582201223627173, 360582200986114648, 360582200748292099, 360582200685551829, 360582200628115459, 360582200419481815]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605795483877810, 360605832535227209⟩, ⟨(-1788219419896106528), (-1786327766579919232)⟩, true⟩

def words08 : List Nat := [360582200210615677, 360582200029331507, 360582200115193534, 360582200246181497, 360582200247174591, 360582200229357731, 360582200340228887, 360582200465047487, 360582200734052064, 360582201047793786]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580719347655039, 360580756409285992⟩, ⟨107417916625748391, 109310347174333687⟩, true⟩

def words09 : List Nat := [360582201241722070, 360582201435760259, 360582201625608346, 360582201918069317, 360582202114174753, 360582202310446198, 360582202407710311, 360582202408787145, 360582202331211183, 360582202313349145]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk755

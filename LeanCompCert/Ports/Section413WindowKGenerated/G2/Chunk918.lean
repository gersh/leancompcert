import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk918

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565713528577658, 360565769007690186⟩, ⟨1483489826030348891, 1486928969802062009⟩, true⟩

def state01 : KState := ⟨⟨360568972103477160, 360569027595080666⟩, ⟨1184319704523552712, 1187759995028829726⟩, true⟩

def words00 : List Nat := [360581966315652760, 360581966259043230, 360581966106734121, 360581965884544442, 360581965662162805, 360581965343436125, 360581965122337529, 360581965019989112, 360581964917506316, 360581964747842118]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573152956922442, 360573208461073028⟩, ⟨800521473565670086, 803962916081583696⟩, true⟩

def words01 : List Nat := [360581964608004225, 360581964587065070, 360581964661761981, 360581964695334855, 360581964696559003, 360581964629206075, 360581964561608456, 360581964457853392, 360581964413434670, 360581964319448999]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580723444419896, 360580778961202930⟩, ⟨105268982313919159, 108711584804502091⟩, true⟩

def words02 : List Nat := [360581964225273759, 360581964064659271, 360581963833604528, 360581963721407148, 360581963608861339, 360581963466127520, 360581963328412526, 360581963118596960, 360581962908522438, 360581962796385382]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574241094244102, 360574296623550721⟩, ⟨700630365207149538, 704074117801446614⟩, true⟩

def words03 : List Nat := [360581962866671978, 360581962950109127, 360581962951312458, 360581962949505630, 360581962950616627, 360581962928265138, 360581963000105984, 360581963016692901, 360581963017885475, 360581962935809013]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596946954327382, 360597002496160085⟩, ⟨(-1384781407060342098), (-1381336504008652668)⟩, true⟩

def words04 : List Nat := [360581962888351856, 360581962984089148, 360581963143376238, 360581963302913558, 360581963358582189, 360581963362077846, 360581963363169767, 360581963364144227, 360581963447370979, 360581963612489699]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360600020882508802, 360600076436979378⟩, ⟨(-1667155890948271251), (-1663709827045881107)⟩, true⟩

def words05 : List Nat := [360581963695634262, 360581963778918799, 360581963934491124, 360581964181604265, 360581964398680473, 360581964615968740, 360581964762191034, 360581964873987962, 360581965072226230, 360581965270901871]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592033008798968, 360592088575786263⟩, ⟨(-933421322393276758), (-929974108642004046)⟩, true⟩

def words06 : List Nat := [360581965407758834, 360581965490800047, 360581965500222452, 360581965509778258, 360581965510891991, 360581965487907395, 360581965631321835, 360581965775014714, 360581965856346120, 360581965967905191]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606499632314200, 360606555211834753⟩, ⟨(-2262602173446338751), (-2259153808203457187)⟩, true⟩

def words07 : List Nat := [360581966068366128, 360581966169234519, 360581966388021065, 360581966522699491, 360581966545245573, 360581966567871391, 360581966679455830, 360581966850694582, 360581967119382067, 360581967388365228]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584718240935339, 360584773833139321⟩, ⟨(-261266955324311698), (-257817424668419572)⟩, true⟩

def words08 : List Nat := [360581967582071849, 360581967778958996, 360581967993637712, 360581968208706069, 360581968321168414, 360581968322496880, 360581968316850161, 360581968250514768, 360581968183944860, 360581968145698022]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360568861062734271, 360568916667443039⟩, ⟨1195990339687642583, 1199441019473461079⟩, true⟩

def words09 : List Nat := [360581968253522055, 360581968361598086, 360581968410072243, 360581968440307887, 360581968441419633, 360581968442207538, 360581968477593779, 360581968478922404, 360581968396982230, 360581968256338289]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk918

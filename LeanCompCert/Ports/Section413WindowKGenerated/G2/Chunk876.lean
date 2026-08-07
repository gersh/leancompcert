import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk876

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580360043234450, 360580410378748567⟩, ⟨148168749420436517, 151146420981751333⟩, true⟩

def state01 : KState := ⟨⟨360559489617780835, 360559539965170047⟩, ⟨1976504945889424579, 1979483657767818455⟩, true⟩

def words00 : List Nat := [360582135800359596, 360582135801620719, 360582135697039034, 360582135527410900, 360582135357590651, 360582135098727871, 360582134917001144, 360582134719194346, 360582134521257799, 360582134231324229]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 87600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 87600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574138016719072, 360574188376033098⟩, ⟨693097609817571157, 696077366485702979⟩, true⟩

def words01 : List Nat := [360582133974450863, 360582133817303508, 360582133659764546, 360582133632562397, 360582133513888231, 360582133258917942, 360582133003711458, 360582132826742732, 360582132740286473, 360582132650930219]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 87610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 87600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590732556819307, 360590782928139959⟩, ⟨(-761120885311303581), (-758140076562513531)⟩, true⟩

def words02 : List Nat := [360582132561387696, 360582132406834029, 360582132152320472, 360582132028253182, 360582131903842343, 360582131745153154, 360582131656097292, 360582131502048591, 360582131347758845, 360582131422661732]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 87620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 87600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564479622995244, 360564530006211834⟩, ⟨1539622887047437405, 1542604738296344109⟩, true⟩

def words03 : List Nat := [360582131652443556, 360582131882462071, 360582132007260733, 360582132050417120, 360582132051475689, 360582132018174104, 360582131984510022, 360582131932839996, 360582131811593287, 360582131612080118]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 87630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 87600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590834864509301, 360590885259632089⟩, ⟨(-770246004798984902), (-767263110030926960)⟩, true⟩

def words04 : List Nat := [360582131412262367, 360582131342851648, 360582131470034992, 360582131599382732, 360582131617966854, 360582131619234709, 360582131600113488, 360582131538478218, 360582131543435078, 360582131644613083]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 87640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 87600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360572321292609536, 360572371699760311⟩, ⟨852594760268173325, 855578709348477569⟩, true⟩

def words05 : List Nat := [360582131680650158, 360582131716817001, 360582131753847588, 360582131891651096, 360582131976387181, 360582132061327008, 360582132070777491, 360582132072040081, 360582132004828187, 360582131894938825]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566848836155988, 360566899255205494⟩, ⟨1332276269189414114, 1335261261371465654⟩, true⟩

def words06 : List Nat := [360582131784636847, 360582131671034815, 360582131469442965, 360582131202861083, 360582130936079431, 360582130620163038, 360582130382853377, 360582130216970700, 360582130050945741, 360582129793147453]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592775176085680, 360592825607038060⟩, ⟨(-940839026406572167), (-937852990640047629)⟩, true⟩

def words07 : List Nat := [360582129620443883, 360582129578070488, 360582129588665904, 360582129589928443, 360582129558236508, 360582129402660020, 360582129246843634, 360582129174602205, 360582129289688307, 360582129412986441]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588438779596230, 360588489222584088⟩, ⟨(-560652360732881226), (-557665269636439048)⟩, true⟩

def words08 : List Nat := [360582129436706827, 360582129464034089, 360582129621011944, 360582129778357187, 360582129839064188, 360582129857086115, 360582129858221374, 360582129811378967, 360582129764313258, 360582129786956300]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582283439329585, 360582333894210247⟩, ⟨(-20814059698607894), (-17825925662892792)⟩, true⟩

def words09 : List Nat := [360582129990386637, 360582130194063051, 360582130332494013, 360582130373569265, 360582130381810781, 360582130390427200, 360582130528502629, 360582130629186141, 360582130632631649, 360582130636258082]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk876

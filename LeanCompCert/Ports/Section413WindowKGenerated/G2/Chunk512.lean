import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk512

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602892297007605, 360602908774156045⟩, ⟨(-1072884487521140891), (-1072314452820233063)⟩, true⟩

def state01 : KState := ⟨⟨360570227000370874, 360570243484264415⟩, ⟨599597909365538578, 600168289448647698⟩, true⟩

def words00 : List Nat := [360581965759420815, 360581965760128866, 360581965814761754, 360581966032829983, 360581966033438247, 360581965889661924, 360581965365383467, 360581964579408276, 360581963793328038, 360581963232154450]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360543006524598065, 360543023015168467⟩, ⟨1993800415923017299, 1994371137961221829⟩, true⟩

def words01 : List Nat := [360581963065126645, 360581963127097107, 360581963127728089, 360581962960405789, 360581962593592926, 360581962131700503, 360581961669613269, 360581961587978327, 360581961126030449, 360581960366553888]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580514232889042, 360580530730141334⟩, ⟨72392491475335702, 72963555793803192⟩, true⟩

def words02 : List Nat := [360581959606945488, 360581958785289301, 360581958155967149, 360581957842754945, 360581957529498931, 360581956897336891, 360581956275497207, 360581955712051592, 360581955148413141, 360581954965077774]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584234800731942, 360584251304737131⟩, ⟨(-118357325822240505), (-117785915519040829)⟩, true⟩

def words03 : List Nat := [360581954937908429, 360581954720164447, 360581954502305987, 360581954120038198, 360581953929926464, 360581953644833175, 360581953359679446, 360581952883310891, 360581952593620265, 360581952639302830]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567599132531778, 360567615643208506⟩, ⟨734133500934833688, 734705253119989234⟩, true⟩

def words04 : List Nat := [360581953064695129, 360581953110297764, 360581953110931192, 360581952895854622, 360581952680670173, 360581952283044147, 360581952130617063, 360581951968520027, 360581951806356136, 360581951355464506]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360612827174104095, 360612843691467244⟩, ⟨(-1584036915315829052), (-1583464820418133278)⟩, true⟩

def words05 : List Nat := [360581951076321855, 360581951055773691, 360581951314462536, 360581951615219844, 360581951615881178, 360581951534335774, 360581951750117827, 360581952240448213, 360581952843666360, 360581953447023747]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607549900991227, 360607566425105337⟩, ⟨(-1313632384251701564), (-1313059943265543720)⟩, true⟩

def words06 : List Nat := [360581953758619268, 360581953976130693, 360581954573126535, 360581955170314181, 360581955672281282, 360581955794783842, 360581955795416186, 360581955676926568, 360581955736891839, 360581956237216169]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552823202154377, 360552839732941390⟩, ⟨1492502231218598283, 1493075014357962663⟩, true⟩

def words07 : List Nat := [360581956660950493, 360581957084805938, 360581957308634302, 360581957311439334, 360581957312043619, 360581957056893556, 360581956803519335, 360581956804228354, 360581956427430859, 360581955860366468]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586189865784160, 360586206403276497⟩, ⟨(-218618362762056085), (-218045235741781363)⟩, true⟩

def words08 : List Nat := [360581955293164823, 360581954892698944, 360581955224688091, 360581955580744733, 360581955610017715, 360581955610726880, 360581955289169444, 360581955318517601, 360581955319102499, 360581955263003510]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580164992806275, 360580181537057691⟩, ⟨90381277755516216, 90954751481364682⟩, true⟩

def words09 : List Nat := [360581955263641450, 360581955105617920, 360581954947468625, 360581954964040568, 360581954986534952, 360581955009156450, 360581955009788292, 360581954842259362, 360581954567904953, 360581954534162591]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk512
